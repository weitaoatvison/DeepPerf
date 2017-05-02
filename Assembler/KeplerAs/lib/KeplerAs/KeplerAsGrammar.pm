package KeplerAs::KeplerAsGrammar;

use strict;
use Carp;
use Exporter;
use Data::Dumper;
our @ISA = qw(Exporter);

our @EXPORT = qw(
    %grammar %flags
    parseInstruct genCode genReuseCode
    processAsmLine processSassLine processSassCtrlLine
    replaceXMADs printCtrl readCtrl getRegNum getVecRegisters getAddrVecRegisters
);

require 5.10.0;

# Helper functions for operands
sub getI
{
    my ($orig, $pos, $mask) = @_;
    my $val = $orig;
    my $neg = $val =~ s|^\-||;

    # parse out our custom index immediates for addresses
    if ($val  =~ m'^(\d+)[xX]<([^>]+)>')
    {
        # allow any perl expression and multiply result by leading decimal.
        # also allow global scalar varibles in the expression.
        my $mul = $1;
        my $exp = $2;
        # strip leading zeros (don't interpret numbers as octal)
        $exp =~ s/(?<!\d)0+(?=[1-9])//g;
        my @globals = $exp =~ m'\$\w+'g;
        my $our = @globals ? ' our (' . join(',',@globals) . ');' : '';
        $val = $mul * eval "package KeplerAs::KeplerAs::CODE;$our $exp";
        #print "$val = $mul x $exp\n"; # if $our;
    }
    # hexidecial value
    elsif ($val  =~ m'^0x[0-9a-zA-Z]+')
    {
        $val = hex($val);
    }
    # otherwise val is a simple decimal value that doesn't need to be modified

    if ( $neg )
    {
        # if the mask removes the sign bit the "neg" flag adds it back on the code somewhere else
        $val = -$val;
        $val &= $mask;
    }
    if (($val & $mask) != $val)
    {
        die sprintf "Immediate value out of range(0x%x): 0x%x ($orig)\n", $mask, $val;
    }
    return $val << $pos;
}
sub getF
{
    #trunc means shift to right for $trunc bits
    my ($val, $pos, $type, $trunc) = @_;
    # hexidecial value
    if ($val  =~ m'^0x[0-9a-zA-Z]+')
    {
        $val = hex($val);
    }
    # support infinity
    elsif ($val =~ m'INF'i)
    {
        $val = $trunc ? ($type eq 'f' ? 0x7f800 : 0x7ff00) : 0x7f800000;
    }
    else
    {
        $val = unpack(($type eq 'f' ? 'L' : 'Q'), pack $type, $val);

        # strip off sign bit if truncating.  It will added elsewhere in the code by the flag capture.
        $val = ($val >> $trunc) & 0x7ffff if $trunc;
    }
    return $val << $pos;
}
sub getR
{
    my ($val, $pos) = @_;
    if ($val =~ m'^R(\d+|Z)$' && $1 < 255)
    {
        $val = $1 eq 'Z' ? 0xff : $1;
    }
    else
    {
        die "Bad register name found: $val\n";
    }
    return $val << $pos;
}
sub getP
{
    my ($val, $pos) = @_;
    if ($val =~ m'^P(\d|T)$' && $1 < 7)
    {
        $val = $1 eq 'T' ? 7 : $1;
    }
    else
    {
        die "Bad predicate name found: $val\n";
    }
    return $val << $pos;
}
#14 bits const immediate start at 23
sub getC { ((hex($_[0]) >> 2) & 0x3fff) << 23 }
#sub getC { ((hex($_[0]) >> 2) & 0x7fff) << 20 }

# Map operands into their value and position in the op code.
my %operands =
(
    #pdstn
    p0      => sub { getP($_[0], 2)  },
    #p0      => sub { getP($_[0], 0)  },
    #pdst
    p3      => sub { getP($_[0], 5)  },
    #p3      => sub { getP($_[0], 3)  },
    #psrc1
    p12     => sub { getP($_[0], 14) },
    #p12     => sub { getP($_[0], 12) },
    #psrc2
    p29     => sub { getP($_[0], 32) },
    #p29     => sub { getP($_[0], 29) },
    #psrc3
    p39     => sub { getP($_[0], 42) },
    #p39     => sub { getP($_[0], 39) },
    #psrc4
    p45     => sub { getP($_[0], 48) },
    #p45     => sub { getP($_[0], 45) },
    #pdst2: SHFL
    p48     => sub { getP($_[0], 51) },
    #p48     => sub { getP($_[0], 48) },
    p58     => sub { getP($_[0], 58) },
    # dest register
    r0      => sub { getR($_[0], 2)  },
    #r0      => sub { getR($_[0], 0)  },
    # src1 register
    r8      => sub { getR($_[0], 10)  },
    #r8      => sub { getR($_[0], 8)  },
    #src2 register
    r20     => sub { getR($_[0], 23) },
    #r20     => sub { getR($_[0], 20) },
    r28     => sub { getR($_[0], 28) },
    #src3 used as 2nd source register in 4 operands instructions like IMAD
    r39s20  => sub { getR($_[0], 42) },
    #r39s20  => sub { getR($_[0], 39) },
    # src3 register
    r39     => sub { getR($_[0], 42) },
    #r39     => sub { getR($_[0], 39) },
    r39a    => sub { getR($_[0], 39) }, # does not modify op code, xor the r39 value again to whipe it out, register must be in sequence with r20
    #constant memory immediate
    c20     => sub { getC($_[0])     },
    z20     => sub { getC($_[0])     },
    #const memory immediate
    c39     => sub { getC($_[0])     },
    #constant memory index cmem_idx
    c34     => sub { hex($_[0]) << 37 },
    #c34     => sub { hex($_[0]) << 34 },
    #const memory index LDC
    c36     => sub { hex($_[0]) << 39 },
    #c36     => sub { hex($_[0]) << 36 },
    #LIMM
    f20w32  => sub { getF($_[0], 23, 'f')        },
    #float immediate 41~23, 12 means shift right 12 bits
    f20     => sub { getF($_[0], 23, 'f', 12)    },
    #f20     => sub { getF($_[0], 20, 'f', 12)    },
    d20     => sub { getF($_[0], 23, 'd', 44)    },
    #d20     => sub { getF($_[0], 20, 'd', 44)    },
    #baroff
    i8w4    => sub { getI($_[0], 10,  0xf)        },
    #i8w4    => sub { getI($_[0], 8,  0xf)        },
    #I3BIMM
    i20     => sub { getI($_[0], 23, 0x7ffff)    },
    #i20     => sub { getI($_[0], 20, 0x7ffff)    },
    i20w6   => sub { getI($_[0], 23, 0x3f)       },
    #i20w6   => sub { getI($_[0], 20, 0x3f)       },
    i20w7   => sub { getI($_[0], 23, 0x7f)       },
    #i20w7   => sub { getI($_[0], 20, 0x7f)       },
    i20w8   => sub { getI($_[0], 23, 0xff)       },
    #SFLNIMM
    #i20w8   => sub { getI($_[0], 20, 0xff)       },
    i20w12  => sub { getI($_[0], 23, 0xfff)      },
    #i20w12  => sub { getI($_[0], 20, 0xfff)      },
    #shared, local memory STL
    i20w24  => sub { getI($_[0], 23, 0xffffff)   },
    #i20w24  => sub { getI($_[0], 20, 0xffffff)   },
    #long immedate
    i20w32  => sub { getI($_[0], 23, 0xffffffff) },
    #i20w32  => sub { getI($_[0], 20, 0xffffffff) },
    #TLD mask
    i31w4   => sub { getI($_[0], 34, 0xf)        },
    #i31w4   => sub { getI($_[0], 31, 0xf)        },
    #SFLMIMM
    i34w13  => sub { getI($_[0], 37, 0x1fff)     },
    #i34w13  => sub { getI($_[0], 34, 0x1fff)     },
    i36w20  => sub { getI($_[0], 36, 0xfffff)    },
    #need to check LEA, width changed from 8 to 5
    #shift ISCADD, shcnt
    i39w8   => sub { getI($_[0], 42, 0x1f)       },
    #i39w8   => sub { getI($_[0], 39, 0xff)       },
    i28w8   => sub { getI($_[0], 28, 0xff)       },
    i28w20  => sub { getI($_[0], 31, 0xfffff)    },
    #i28w20  => sub { getI($_[0], 28, 0xfffff)    },
    i48w8   => sub { getI($_[0], 48, 0xff)       },
    i51w5   => sub { getI($_[0], 51, 0x1f)       },
    i53w5   => sub { getI($_[0], 53, 0x1f)       },
    #SHFIMM: SHR, SHL
    i23w6  => sub { getI($_[0], 23, 0x3f)      },
);

# Rules for operands and their closely tied flags
my $hex     = qr"0[xX][0-9a-fA-F]+";
my $iAddr   = qr"\d+[xX]<[^>]+>";
my $immed   = qr"$hex|$iAddr|\d+"o;
my $reg     = qr"[a-zA-Z_]\w*"; # must start with letter or underscore\
my $p       = qr"P[0-6T]";
my $noPred  = qr"(?<noPred>)";
my $pred    = qr"\@(?<predNot>\!)?P(?<predNum>[0-6]) ";
my $p0      = qr"(?<p0>$p)"o;
my $p3      = qr"(?<p3>$p)"o;
my $p12     = qr"(?<p12not>\!)?(?<p12>$p)"o;
my $p29     = qr"(?<p29not>\!)?(?<p29>$p)"o;
#example: ISETP.EQ.U32.XOR P0, PT, R0, R3, !P0;
my $p39     = qr"(?<p39not>\!)?(?<p39>$p)"o;
my $p45     = qr"(?<p45>$p)"o;
my $p48     = qr"(?<p48>$p)"o;
my $p58     = qr"(?<p58>$p)"o;
#dst
my $r0      = qr"(?<r0>$reg)";
#dest
#CC acout32
my $r0cc    = qr"(?<r0>$reg)(?<CC>\.CC)?";
#src1
my $r8      = qr"(?<r8neg>\-)?(?<r8abs>\|)?(?<r8>$reg)\|?(?:\.(?<r8part>H0|H1|B0|B1|B2|B3|H0_H0|H1_H1))?(?<reuse1>\.reuse)?";
#src2
my $r20     = qr"(?<r20neg>\-)?(?<r20abs>\|)?(?<r20>$reg)\|?(?:\.(?<r20part>H0|H1|B0|B1|B2|B3|H0_H0|H1_H1))?(?<reuse2>\.reuse)?";
my $r28     = qr"(?<r28>$reg)";
my $r39s20  = qr"(?<r20neg>\-)?(?<r20abs>\|)?(?<r39s20>(?<r20>$reg))\|?(?:\.(?<r39part>H0|H1))?(?<reuse2>\.reuse)?";
#src3
my $r39     = qr"(?<r39neg>\-)?(?<r39>$reg)(?:\.(?<r39part>H0|H1))?(?<reuse3>\.reuse)?";
my $r39a    = qr"(?<r39a>(?<r39>$reg))(?<reuse3>\.reuse)?";
#const memory c[][]
my $c20     = qr"(?<r20neg>\-)?(?<r20abs>\|)?c\[(?<c34>$hex)\]\s*\[(?<c20>$hex)\]\|?(?:\.(?<r20part>H0|H1|B0|B1|B2|B3))?"o;
#my $z20     = qr"(?<r20neg>\-)?(?<r20abs>\|)?c\[(?<c34>$hex)\]\s*\[(?<z20>$hex)\]\|?(?:\.(?<r20part>H0|H1|B0|B1|B2|B3))?"o;
my $c20x    = qr"(?<r20neg>\-)?(?<r20abs>\|)?c\[(?<c34>$hex)\]\s*\[(?<c20>$hex)\]\|?(?:\.(?<r20partx>H0|H1|B0|B1|B2|B3))?"o;
my $c20s39  = qr"(?<r39neg>\-)?c\[(?<c34>$hex)\]\s*\[(?<c39>$hex)\]"o;
my $f20w32  = qr"(?<f20w32>(?:\-|\+|)(?i:$hex|inf\s*|\d+(?:\.\d+(?:e[\+\-]\d+)?)?))";
my $f20     = qr"(?<f20>(?:(?<neg>\-)|\+|)(?i:inf\s*|\d+(?:\.\d+(?:e[\+\-]\d+)?)?))(?<r20neg>\.NEG)?"o;
my $d20     = qr"(?<d20>(?:(?<neg>\-)|\+|)(?i:inf\s*|\d+(?:\.\d+(?:e[\+\-]\d+)?)?))(?<r20neg>\.NEG)?"o;
my $i8w4    = qr"(?<i8w4>$immed)"o;
#neg: bit 59 sign flag
my $i20     = qr"(?<i20>(?<neg>\-)?$immed)(?<r20neg>\.NEG)?"o;
my $i20w6   = qr"(?<i20w6>$immed)"o;
my $i20w7   = qr"(?<i20w7>$immed)"o;
my $i20w8   = qr"(?<i20w8>$immed)"o;
my $i20w12  = qr"(?<i20w12>$immed)"o;
my $i20w24  = qr"(?<i20w24>\-?$immed)"o;
my $i20w32  = qr"(?<i20w32>\-?$immed)"o;
my $i39w8   = qr"(?<i39w8>\-?$immed)"o;
my $i28w8   = qr"(?<i28w8>$immed)"o;
my $i28w20  = qr"(?<i28w20>\-?$immed)"o;
my $i31w4   = qr"(?<i31w4>$immed)"o;
my $i34w13  = qr"(?<i34w13>$immed)"o;
my $i36w20  = qr"(?<i36w20>$immed)"o;
my $i48w8   = qr"(?<i48w8>$immed)"o;
my $i51w5   = qr"(?<i51w5>$immed)"o;
my $i53w5   = qr"(?<i53w5>$immed)"o;
my $i23w6   = qr"(?<i23w6>$immed)"o;
my $ir20    = qr"$i20|$r20"o;
my $cr20    = qr"$c20|$r20"o;
my $icr20   = qr"$i20|$c20|$r20"o;
my $fcr20   = qr"$f20|$c20|$r20"o;
my $cr39    = qr"$c20s39|$r39"o;
my $dr20    = qr"$d20|$r20"o;

# Instruction specific rules for capturing various flags
my $u32   = qr"(?<U32>\.U32)?";
my $REV2B = qr"(?<REV2B>\.REV2B)?";
my $W     = qr"(?<W>\.W)?";
my $pnot2d= qr"(?<PNOT2D>\.PNOT2D)?";
my $ftz   = qr"(?<FTZ>\.FTZ)?";
my $sat   = qr"(?<SAT>\.SAT)?";
my $rnd   = qr"(?:\.(?<rnd>RN|RM|RP|RZ))?";
#mulf:div2|div4|div8|mul8|mul4|mul2
my $mulf  = qr"(?:\.(?<mulf>D2|D4|D8|M8|M4|M2))?";
my $condition  = qr"(?:(?<CON>F|LT|EQ|LE|GT|NE|GE|NUM|NAN|LTU|EQU|LEU|GTU|NEU|GEU|OFF|LO|SFF|LS|HI|SFT|HS|OFT))?";
#my $condition  = qr"(?:(?<CON>NEVER|L|E|LE|G|LG|GE|LGE|U|LU|EU|LEU|GU|LGU|GEU|NO|NC|NS|NA|A|S|C|O))?";
my $lane2a= qr"(?:\.(?<lane2a>LNONE|L0|L1|L01|L2|L02|L12|L012|L3|L03|L13|L013|L23|L023|L123))?";
my $lane0e= qr"(?:\.(?<lane0e>LNONE|L0|L1|L01|L2|L02|L12|L012|L3|L03|L13|L013|L23|L023|L123))?";

#MOV: lane2a
#0x0000000000000000 LNONE
#0x0000040000000000 L0
#0x0000080000000000 L1
#0x00000c0000000000 L01
#0x0000100000000000 L2
#0x0000140000000000 L02
#0x0000180000000000 L012
#0x00001c0000000000 L012
#0x0000200000000000 L3
#0x0000240000000000 L03
#0x0000280000000000 L13
#0x00002c0000000000 L013
#0x0000300000000000 L23
#0x0000340000000000 L023
#0x0000380000000000 L123
#0x00003c0000000000

my $round = qr"(?:\.(?<round>ROUND|FLOOR|CEIL|TRUNC))?";
my $fcmp  = qr"(?<cmp>\.LT|\.EQ|\.LE|\.GT|\.NE|\.GE|\.NUM|\.NAN|\.LTU|\.EQU|\.LEU|\.GTU|\.NEU|\.GEU|)";
my $icmp  = qr"\.(?<cmp>LT|EQ|LE|GT|NE|GE)";
my $bool  = qr"\.(?<bool>AND|OR|XOR|PASS_B)";
my $bool2 = qr"\.(?<bool2>AND|OR|XOR)";
my $func  = qr"\.(?<func>COS|SIN|EX2|LG2|RCP|RSQ|RCP64H|RSQ64H)";
my $rro   = qr"\.(?<func>SINCOS|EX2)";
my $add3  = qr"(?:\.(?<type>X|RS|LS))?";
my $lopz  = qr"(?:\.(?<z>NZ|Z) $p48,|(?<noz>))"o;
#acin34 flag
my $X     = qr"(?<X>\.X)?";
#IADD.PO 52~51:11
my $PO     = qr"(?<PO>\.PO)?";
#.BF:ISET, PSET
my $bf     = qr"(?<BF>\.BF)?";
#join flag
#bpt_TODO,JCAL,CAL,PRET,prelongjmp_TODO,SSY,PBK,PCNT
my $S     = qr"(?<S>\.S)?";
my $tld   = qr"(?<NODEP>NODEP\.)?(?:(?<reuse1>T)|(?<reuse2>P))";
my $chnls = qr"(?<chnls>R|RGBA)";
my $sr    = qr"SR_(?<sr>\S+)";
#0x0000000000000000 LANEID
#0x0000000001000000 NPHYSID
#0x0000000001800000 PHYSID
#0x0000000002000000 PM0
#0x0000000002800000 PM1
#0x0000000003000000 PM2
#0x0000000003800000 PM3
#0x0000000004000000 PM4
#0x0000000004800000 PM5
#0x0000000005000000 PM6
#0x0000000005800000 PM7
#0x0000000008000000 VTXCNT
#0x0000000008800000 INVOC
#0x0000000009000000 YDIR
#0x0000000010000000 TID
#0x0000000010800000 TID.X
#0x0000000011000000 TID.Y
#0x0000000011800000 TID.Z
#0x0000000012000000 LAUNCHARG
#0x0000000012800000 CTAID.X
#0x0000000013000000 CTAID.Y
#0x0000000013800000 CTAID.Z
#0x0000000014000000 NTID
#0x0000000014800000 NTID.X
#0x0000000015000000 NTID.Y
#0x0000000015800000 NTID.Z
#0x0000000016000000 GRIDID
#0x0000000016800000 NCTAID.X
#0x0000000017000000 NCTAID.Y
#0x0000000017800000 NCTAID.Z
#0x0000000018000000 SWINBASE
#0x0000000018800000 SWINSZ
#0x0000000019000000 SMEMSZ
#0x0000000019800000 SMEMBANKS
#0x000000001a000000 LWINBASE
#0x000000001a800000 LWINSZ
#0x000000001b000000 LPOSSZ
#0x000000001b800000 LNEGSTART
#0x000000001c000000 LANEMASK_EQ
#0x000000001c800000 LANEMASK_LT
#0x000000001d000000 LANEMASK_LE
#0x000000001d800000 LANEMASK_GT
#0x000000001e000000 LANEMASK_GE
#0x0000000020000000 TRAPSTAT
#0x0000000021000000 WARPERR
#0x0000000029000000 CLOCK
#0x0000000029800000 CLOCKHI
my $shf   = qr"(?<W>\.W)?(?:\.(?<type>U64|S64))?(?<HI>\.HI)?";
#my $xmad  = qr"(?:\.(?<type1>U16|S16))?(?:\.(?<type2>U16|S16))?(?:\.(?<mode>MRG|PSL|CHI|CLO|CSFU))?(?<CBCC>\.CBCC)?";
my $imad  = qr"(?:\.(?<type1>U32|S32))?(?:\.(?<type2>U32|S32))?(?:\.(?<mode>MRG|PSL|CHI|CLO|CSFU))?(?<CBCC>\.CBCC)?";
my $imadc = qr"(?:\.(?<type1>U32|S32))?(?:\.(?<type2>U32|S32))?(?:\.(?<modec>MRG|PSL|CHI|CLO|CSFU))?(?<CBCC>\.CBCC)?";
my $imul  = qr"(?:\.(?<type1>U32|S32))?(?:\.(?<type2>U32|S32))?";
#my $xmadc = qr"(?:\.(?<type1>U16|S16))?(?:\.(?<type2>U16|S16))?(?:\.(?<modec>MRG|PSL|CHI|CLO|CSFU))?(?<CBCC>\.CBCC)?";
my $vmad8 = qr"\.(?<sign1>[SU])(?<size1>8|16)\.(?<sign2>[SU])(?<size2>8|16)(?<PO>\.PO)?(?<SHR_7>\.SHR_7)?(?<SHR_15>\.SHR_15)?(?<SAT>\.SAT)?";
my $vmad16= qr"\.(?<sign1>[SU])(?<size1>16)\.(?<sign2>[SU])(?<size2>16)";
my $hilo  = qr"(?:\.(?<mode>XHI|XLO))?";
my $hi  = qr"(?:\.(?<mode>HI))?";
my $vaddType = qr"(?:\.(?<UD>UD))?(?:\.(?<SD>SD))?(?:\.(?<sign1>[SU])(?<size1>8|16|32))?(?:\.(?<sign2>[SU])(?<size2>8|16|32))?";
my $vaddMode = qr"(?:\.(?<mode>MRG_16[HL]|MRG_8B[0-3]|ACC|MIN|MAX))?";
my $vmnmx = qr"(?:\.(?<MX>MX))?";
my $x2x   = qr"\.(?<destSign>F|U|S)(?<destWidth>8|16|32|64)\.(?<srcSign>F|U|S)(?<srcWidth>8|16|32|64)";
my $prmt  = qr"(?:\.(?<mode>F4E|B4E|RC8|ECL|ECR|RC16))?";
my $shfl  = qr"\.(?<mode>IDX|UP|DOWN|BFLY)";
my $bar   = qr"\.(?<mode>SYNC|ARV|RED)(?:\.(?<red>POPC|AND|OR))? (?:$i8w4|$r8)(?:, (?:$i20w12|$r20))?(?(<r20>)|(?<nor20>))(?(<red>), $p39|(?<nop39>))"o;
my $b2r   = qr"\.RESULT $r0(?:, $p45|(?<nop45>))"o;
my $dbar  = qr"(?<SB>SB0|SB1|SB2|SB3|SB4|SB5)";
my $dbar2 = qr" {(?<db5>5)?,?(?<db4>4)?,?(?<db3>3)?,?(?<db2>2)?,?(?<db1>1)?,?(?<db0>0)?}";
my $mbar  = qr"\.(?<mode>CTA|GL|SYS)";
my $addr  = qr"\[(?:(?<r8>$reg)|(?<nor8>))(?:\s*\+?\s*$i20w24)?\]"o;
#gamem, ATOM, RED
my $addr2 = qr"\[(?:(?<r8>$reg)|(?<nor8>))(?:\s*\+?\s*$i28w20)?\]"o;
my $ldc   = qr"c\[(?<c36>$hex)\]\s*$addr"o;
my $atom  = qr"(?<E>\.E)?(?:\.(?<mode>ADD|MIN|MAX|INC|DEC|AND|OR|XOR|EXCH|CAS))(?<type>|\.S32|\.U64|\.F(?:16x2|32)\.FTZ\.RN|\.S64|\.64)";
my $vote  = qr"\.(?<mode>ALL|ANY|EQ)"o;
my $memType  = qr"(?<type>\.U8|\.S8|\.U16|\.S16||\.32|\.64|\.128)";
my $memTypeX  = qr"(?<type>\.b32|\.b64|\.b96|\.b128)";
my $memCache = qr"(?<E>\.E)?(?<U>\.U)?(?:\.(?<cache>CG|CI|CS|CV|IL|WT|LU))?";
my $ldmemCache = qr"(?<E>\.E)?(?<U>\.U)?(?:\.(?<cache>CG|LU|CV))?";
my $stmemCache = qr"(?<E>\.E)?(?<U>\.U)?(?:\.(?<cache>CG|CS|WT))?";



# class: hardware resource that shares characteristics with types
# lat  : pipeline depth where relevent, placeholder for memory ops
# blat : barrier latency, typical fetch time for memory operations. Highly variable.
# rlat : operand read latency for memory ops
# rhold: clock cycles that a memory op typically holds onto a register before it's free to be written by another op.
# tput : throughput, clock cycles an op takes when two ops of the same class are issued in succession.
# dual : whether this instruction type can be dual issued
# reuse: whether this instruction type accepts register reuse flags.

# Some of these values are guesses and need to be updated from micro benchmarks.
# We may need to split these classes up further.
my $s2rT  = {class => 's2r',   lat => 2,   blat => 25,  rlat => 0, rhold => 0,  tput => 1,   dual => 0, reuse => 0};
my $smemT = {class => 'mem',   lat => 2,   blat => 30,  rlat => 2, rhold => 20, tput => 1,   dual => 1, reuse => 0};
my $gmemT = {class => 'mem',   lat => 2,   blat => 200, rlat => 4, rhold => 20, tput => 1,   dual => 1, reuse => 0};
my $x32T  = {class => 'x32',   lat => 6,   blat => 0,   rlat => 0, rhold => 0,  tput => 1,   dual => 0, reuse => 1};
my $x64T  = {class => 'x64',   lat => 2,   blat => 128, rlat => 0, rhold => 0,  tput => 128, dual => 0, reuse => 1};
my $shftT = {class => 'shift', lat => 6,   blat => 0,   rlat => 0, rhold => 0,  tput => 2,   dual => 0, reuse => 1};
my $cmpT  = {class => 'cmp',   lat => 13,  blat => 0,   rlat => 0, rhold => 0,  tput => 2,   dual => 0, reuse => 1};
my $qtrT  = {class => 'qtr',   lat => 8,   blat => 0,   rlat => 4, rhold => 0,  tput => 1,   dual => 1, reuse => 0};
my $rroT  = {class => 'rro',   lat => 2,   blat => 0,   rlat => 0, rhold => 0,  tput => 1,   dual => 0, reuse => 0};
my $voteT = {class => 'vote',  lat => 2,   blat => 0,   rlat => 0, rhold => 0,  tput => 1,   dual => 0, reuse => 0};


# Create map of op names to rules
#Maxwell only Instructions:ATOMS CCTLT CS2R IADD3 LEA PEXIT R2B STG SUATOM SULD SURED SUST SYNC TEXS TLD4S TLDS XMAD
our %grammar =
(
    #Floating Point Instructions
    FADD     => [
    # { 0x22c0000000000002ull, 0x3fc0000000000003ull, N("add"), T(ftz2f), T(sat35), T(frm2a), N("f32"), DST, T(neg33), T(abs31), SRC1, T(neg30), T(abs34), T(is2) }
    { type => $x32T,  code => 0xe2c0000000000002, rule => qr"^$pred?FADD$ftz$rnd$sat $r0, $r8, $cr20;"o,               },
    #{ 0x02c0000000000001ull, 0x37c0000000000003ull, N("add"), T(ftz2f), T(sat35), T(frm2a), N("f32"), DST, T(neg33), T(abs31), SRC1, T(neg3b), T(fi2) }
    { type => $x32T,  code => 0xc2c0000000000001, rule => qr"^$pred?FADD$ftz$rnd$sat $r0, $r8, $f20;"o,               },
    ],
    #{ 0x4000000000000000ull, 0xf180000000000000ull, T(join), T(p), N("add"), T(ftz3a), N("f32"), DST, T(neg3b), T(abs39), SRC1, LIMM }
    FADD32I  => [ { type => $x32T,  code => 0x4000000000000000, rule => qr"^$pred?FADD32I$ftz $r0, $r8, $f20w32;"o,                   } ],
    #zxx: TODO
    FCHK     => [ { type => $x32T,  code => 0x5c88000000000000, rule => qr"^$pred?FCHK\.DIVIDE $p0, $r8, $r20;"o,                     } ], #Partial?
    #zxx: 0x1d00000000000002, 63, 62 is 11(src2, src3) 10 (src3, const), 01 (const, src3)
    #three source operands,  (const, src3) is dealt differently
    FCMP     => [
    #{ 0x1d00000000000002ull, 0x3f80000000000003ull, N("slct"), T(ftz32), N("b32"), DST, SRC1, T(is2w3), T(setit), N("f32"), T(is3) }
    { type => $cmpT,  code => 0xdd00000000000002, rule => qr"^$pred?FCMP$fcmp$ftz $r0, $r8, $cr20, $r39;"o,            },
    #%constCodes will modify opcode when capture c39 (c20s39)
    { type => $cmpT,  code => 0xdd00000000000002, rule => qr"^$pred?FCMP$fcmp$ftz $r0, $r8, $r39s20, $c20s39;"o,            },
    #{ 0xb500000000000001ull, 0xb780000000000003ull, N("slct"), T(ftz32), N("b32"), DST, SRC1, T(neg3b), FIMM, T(setit), N("f32"), SRC3 }
    { type => $cmpT,  code => 0xb500000000000001, rule => qr"^$pred?FCMP$fcmp$ftz $r0, $r8, $f20, $r39;"o,            },
    ],
    #{ 0x0c00000000000002ull, 0x3e00000000000003ull, N("fma"), T(ftz38), T(sat35),  T(frm36), N("f32"), DS    T, T(neg33), SRC1, T(is2w3), T(neg34), T(is3) }
    FFMA     => [
                  { type => $x32T,  code => 0xcc00000000000002, rule => qr"^$pred?FFMA$ftz$rnd$sat $r0, $r8, $cr20, $r39;"o,         },
                  { type => $x32T,  code => 0xcc00000000000002, rule => qr"^$pred?FFMA$ftz$rnd$sat $r0, $r8, $r39s20, $c20s39;"o,     },
                  #{ 0x9400000000000001ull, 0xb6c0000000000003ull, N("fma"), T(ftz38), T(sat35), T(frm36), N("f32"), DST, T(neg33), SRC1, T(neg3b), FIMM, T(neg34), SRC3 },
                  { type => $x32T,  code => 0x9400000000000001, rule => qr"^$pred?FFMA$ftz$rnd$sat $r0, $r8, $f20, $r39;"o,     },
                ],
    #flag(abs34/r20abs, abs31/r8abs, neg33/r8neg, neg30/r20neg)
    FMNMX    => [
    #{ 0x2300000000000002ull, 0x3fc0000000000003ull, T(minmax), T(ftz2f), N("f32"), DST, T(neg33), T(abs31), SRC1, T(neg30), T(abs34), T(is2) }
    { type => $shftT, code => 0xe300000000000002, rule => qr"^$pred?FMNMX$ftz $r0, $r8, $cr20, $p39;"o,                },
    #{ 0x0300000000000001ull, 0x37c0000000000003ull, T(minmax), T(ftz2f), N("f32"), DST, T(neg33), T(abs31), SRC1, T(neg3b), T(fi2) }
    { type => $shftT, code => 0xc300000000000001, rule => qr"^$pred?FMNMX$ftz $r0, $r8, $f20, $p39;"o,                },
    ],
    FMUL     => [
    #{ 0x2340000000000002ull, 0x3fc0000000000003ull, N("mul"), T(mulf), T(ftz2f), T(sat35), T(frm2a), T(ne    g33), N("f32"), DST, SRC1, T(is2) }
    { type => $x32T,  code => 0xe340000000000002, rule => qr"^$pred?FMUL$ftz$rnd$sat$mulf $r0, $r8, $cr20;"o,               },
    #{ 0x0340000000000001ull, 0x37c0000000000003ull, N("mul"), T(ftz2f), T(sat35), T(frm2a), T(neg3b), N("f32"), DST, SRC1, T(fi2) }
    { type => $x32T,  code => 0xc340000000000001, rule => qr"^$pred?FMUL$ftz$rnd$sat$mulf $r0, $r8, $f20;"o,               },
    ],
    #zxx:TODO double check: 0x2000000000000002ull, 0xfa80000000000003ull
    FMUL32I  => [ { type => $x32T,  code => 0x2000000000000002, rule => qr"^$pred?FMUL32I$ftz $r0, $r8, $f20w32;"o,                   } ],
    #{ 0x0000000000000002ull, 0x38c0000000000003ull, N("set"), T(ftz3a), N("b32"), DST, T(setit), N("f32"), T(neg2e), T(abs39), SRC1, T(neg38), T(abs2f), T(is2), T(setlop) }
    #need to check neg, abs flags
    FSET     => [
    #{ 0x0000000000000002ull, 0x3880000000000003ull, N("set"), T(ftz3a), N("b32"), DST, T(acout32), T(setit), N("f32"), T(neg2e), T(abs39), SRC1, T(neg38), T(abs2f), T(is2), T(setlop3) }
    { type => $shftT, code => 0xc000000000000002, rule => qr"^$pred?FSET$fcmp$ftz$bool $r0, $r8, $cr20, $p39;"o,       },
    #{ 0x8000000000000001ull, 0xf180000000000003ull, N("set"), T(ftz3a), N("b32"), DST, T(acout32), T(setit), N("f32"), T(neg2e), T(abs39), SRC1, T(neg3b), FIMM, T(setlop3) }
    { type => $shftT, code => 0x8000000000000001, rule => qr"^$pred?FSET$fcmp$ftz$bool $r0, $r8, $f20, $p39;"o,       },
    ],
    #0x1d80000000000002ull, 0x3f80000000000003ull #FSETP.EQ.AND P0, PT, R15, RZ, P1
    FSETP    => [ { type => $cmpT,  code => 0xdd80000000000002, rule => qr"^$pred?FSETP$fcmp$ftz$bool $p3, $p0, $r8, $fcr20, $p39;"o, } ],
    # 0x8400000000000002ull, 0xbfc0000000000003ull, T(sfuop), N("f32"), DST, T(neg33), T(abs31),SRC1
    MUFU     => [ { type => $qtrT,  code => 0x8400000000000002, rule => qr"^$pred?MUFU$func $r0, $r8;"o,                              } ],
    #zxx:RRO range reduction operator FP, need to probe on Kepler
    #{ 0x2480000000000002ull, 0x3fc0040000000003ull, N("presin"), N("f32"), DST, T(neg30), T(abs34), T(is2) }
    #{ 0x2480040000000002ull, 0x3fc0040000000003ull, N("preex2"), N("f32"), DST, T(neg30), T(abs34), T(is2) }
    #the 3rd operand shoud be icr20
    RRO      => [ { type => $rroT,  code => 0xe480000000000002, rule => qr"^$pred?RRO$rro $r0, $r20;"o,                               } ],
    DADD     => [
    #{ 0x2380000000000002ull, 0x3fc0000000000003ull, N("add"), T(frm2a), N("f64"), DSTD, T(neg33), T(abs31), SRC1D, T(neg30), T(abs34), T(ds2) }
    { type => $x64T,  code => 0xe380000000000002, rule => qr"^$pred?DADD$rnd $r0, $r8, $cr20;"o,                        },
    #{ 0x0380000000000001ull, 0x37c0000000000003ull, N("add"), T(frm2a), N("f64"), DSTD, T(neg33), T(abs31), SRC1D, T(neg3b), T(di2) }
    { type => $x64T,  code => 0xc380000000000001, rule => qr"^$pred?DADD$rnd $r0, $r8, $d20;"o,                        },
    ],
    #{ 0x1b80000000000002ull, 0x3f80000000000003ull, N("fma"), T(frm35), N("f64"), DSTD, T(neg33), SRC1D, T(ds2w3), T(neg34), T(ds3) }
    DFMA     => [
    { type => $x64T,  code => 0xdb80000000000002, rule => qr"^$pred?DFMA$rnd $r0, $r8, $cr20, $r39;"o,                  },
    #TODO
    { type => $x64T,  code => 0xdb80000000000002, rule => qr"^$pred?DFMA$rnd $r0, $r8, $d20, $r39;"o,                  },
    ],
    #0x2280000000000002ull, 0x3fc0000000000003ull
    DMNMX    => [
    { type => $cmpT,  code => 0xe280000000000002, rule => qr"^$pred?DMNMX $r0, $r8, $cr20, $p39;"o,                     },
    #TODO
    { type => $cmpT,  code => 0xe280000000000002, rule => qr"^$pred?DMNMX $r0, $r8, $d20, $p39;"o,                     },
    ],
    DMUL     => [
    #{ 0x2400000000000002ull, 0x3fc0000000000003ull, N("mul"), T(frm2a), T(neg33), N("f64"), DSTD, SRC1D, T(ds2) }
    { type => $x64T,  code => 0xe400000000000002, rule => qr"^$pred?DMUL$rnd $r0, $r8, $cr20;"o,                        },
    #{ 0x0400000000000001ull, 0x37c0000000000003ull, N("mul"), T(frm2a), T(neg3b), N("f64"), DSTD, SRC1D, T(di2) }
    { type => $x64T,  code => 0xc400000000000001, rule => qr"^$pred?DMUL$rnd $r0, $r8, $d20;"o,                        },
    ],
    #zxx: TODO
    #old{0x0800000000000002ull, 0x3cc0000000000003ull, N("set"), N("b32"), DST, T(setit), N("f64"),
    #T(neg2e), T(abs39), SRC1D, T(neg38), T(abs2f), T(ds2), T(setlop)}
    #new{ 0x0800000000000002ull, 0x3cc0000000000003ull, N("set"), N("b32"), DST, T(acout32),
    #T(setit), N("f64"), T(neg2e), T(abs39), SRC1D, T(neg38), T(abs2f), T(ds2), T(setlop3)},
    DSET     => [ { type => $cmpT,  code => 0xc800000000000002, rule => qr"^$pred?DSET$fcmp$bool $r0, $r8, $dr20, $p39;"o,            } ],
    #{ 0x1c00000000000002ull, 0x3f80000000000003ull, N("set"), PDST, PDSTN, T(setit), N("f64"), T(neg2e), T(abs9), SRC1D, T(neg8), T(abs2f), T(ds2), T(setlop) }
    DSETP    => [ { type => $cmpT,  code => 0xdc00000000000002, rule => qr"^$pred?DSETP$fcmp$bool $p3, $p0, $r8, $dr20, $p39;"o,      } ],
    #zxx: Kepler do not have this instruction
    FSWZADD  => [ { type => $x32T,  code => 0x0000000000000000, rule => qr"^$pred?FSWZADD[^;]*;"o,                                    } ], #TODO

    #zxx: TODO
    HADD2     => [ { type => $x32T,  code => 0x5d10000000000000, rule => qr"^$pred?HADD2$ftz $r0, $r8, $r20;"o,               } ],
    HMUL2     => [ { type => $x32T,  code => 0x5d08000000000000, rule => qr"^$pred?HMUL2$ftz $r0, $r8, $r20;"o,               } ],
    HFMA2     => [ { type => $x32T,  code => 0x5d00000000000000, rule => qr"^$pred?HFMA2$ftz $r0, $r8, $r20, $r39;"o,         } ],
    HSETP2    => [ { type => $cmpT,  code => 0x5d20000000000000, rule => qr"^$pred?HSETP2$fcmp$bool $p3, $p0, $r8, $fcr20, $p39;"o, } ], #Partial

    #Integer Instructions
    BFE       => [
    #default is s32:us32_33 0x0008000000000000
    #{ 0xe000000000000002ull, 0xffc0000000000003ull, N("ext"), T(rev2b), T(us32_33), DST, SRC1, SRC2},  //XXX? can't find CONST
    { type => $shftT,  code => 0xe008000000000002, rule => qr"^$pred?BFE$u32$REV2B $r0, $r8, $cr20;"o,                          },
    #{ 0xc000000000000001ull, 0xffc0000000000003ull, N("ext"), T(rev2b), T(us32_33), DST, SRC1, I3BIMM},
    { type => $shftT,  code => 0xc008000000000001, rule => qr"^$pred?BFE$u32$REV2B $r0, $r8, $ir20;"o,                          },
    ],
    BFI       => [
    #{ 0x1f80000000000002ull, 0x3fc0000000000003ull, N("ins"), N("b32"), DST, SRC1, T(is2w3), T(is3) }
    { type => $shftT,  code => 0xdf80000000000002, rule => qr"^$pred?BFI$S $r0, $r8, $r20, $cr39;"o,                        },
    #{ 0xb780000000000001ull, 0xb7c0000000000003ull, N("ins"), N("b32"), DST, SRC1, I3BIMM, SRC3 }
    { type => $shftT,  code => 0xb780000000000001, rule => qr"^$pred?BFI$S $r0, $r8, $i20, $cr39;"o,                        },
    ],
    #{ 0x2180000000000002ull, 0x3fc0000000000003ull, N("bfind"), T(shiftamt), T(us32_33), DST, T(not2b), T(is2) }
    #shiftamt flag need to be added
    FLO       => [ { type => $s2rT,   code => 0xe180000000000002, rule => qr"^$pred?FLO\.U32 $r0, $icr20;"o,                              } ],
    IADD      => [
    #{ 0x2080000000000002ull, 0x3fc0000000000003ull, T(addop), T(sat35), N("b32"), DST, T(acout32), SRC1, T(is2), T(acin2e) }
    { type => $x32T,   code => 0xe080000000000002, rule => qr"^$pred?IADD$S$PO$sat$X $r0cc, $r8, $cr20;"o,                         },
    #52~51: 00
    #{ 0x0080000000000001ull, 0x37c0000000000003ull, T(addop), T(sat35), N("b32"), DST, T(acout32), SRC1, T(i3bi2) }
    { type => $x32T,   code => 0xc080000000000001, rule => qr"^$pred?IADD$S$PO$sat$X $r0cc, $r8, $i20;"o,                         },
    ],

    ISUB      => [
    #52~51: 01
    #{ 0x2080000000000002ull, 0x3fc0000000000003ull, T(addop), T(sat35), N("b32"), DST, T(acout32), SRC1, T(is2), T(acin2e) }
    { type => $x32T,   code => 0xe088000000000002, rule => qr"^$pred?ISUB$sat$X $r0cc, $r8, $cr20;"o,                         },
    #52~51: 01
    #{ 0x0080000000000001ull, 0x37c0000000000003ull, T(addop), T(sat35), N("b32"), DST, T(acout32), SRC1, T(i3bi2) }
    { type => $x32T,   code => 0xc088000000000001, rule => qr"^$pred?ISUB$sat$X $r0cc, $r8, $i20;"o,                         },
    #{ 0x0080000000000001ull, 0x37c0000000000003ull, T(addop), T(sat35), N("b32"), DST, T(acout32), SRC1, T(i3bi2) }
    #52~51:10
    { type => $x32T,   code => 0xc090000000000001, rule => qr"^$pred?ISUB$sat$X $r0cc, $i20, $r8;"o,                         },
    ],



    #0x4000000000000001ull, 0xf580000000000003ull
    IADD32I   => [ { type => $x32T,   code => 0x4000000000000001, rule => qr"^$pred?IADD32I$X $r0cc, $r8, $i20w32;"o,                         } ],
    #IADD3     => [ { type => $x32T,   code => 0x5cc0000000000000, rule => qr"^$pred?IADD3$add3 $r0cc, $r8, $icr20, $r39;"o,                 } ],
    #default is s32, not u32
    ICMP      => [
    #{ 0x1a00000000000002ull, 0x3fc0000000000003ull, N("slct"), N("b32"), DST, SRC1, T(is2w3), T(isetit), T(us32_33), T(is3) }
    { type => $cmpT,   code => 0xda08000000000002, rule => qr"^$pred?ICMP$icmp$u32 $r0, $r8, $cr20, $r39;"o,              },
    { type => $cmpT,   code => 0xda08000000000002, rule => qr"^$pred?ICMP$icmp$u32 $r0, $r8, $r39s20, $c20s39;"o,              },
    #{ 0xb200000000000001ull, 0xb780000000000003ull, N("slct"), N("b32"), DST, SRC1, I3BIMM, T(isetit), T(us32_33), SRC3 }
    { type => $cmpT,   code => 0xb208000000000001, rule => qr"^$pred?ICMP$icmp$u32 $r0, $r8, $i20, $r39;"o,              },
    ],
    IMNMX     => [
    #{ 0x2100000000000002ull, 0x3fc0000000000003ull, T(minmax), T(us32_33), DST, SRC1, T(is2) },
    { type => $shftT,  code => 0xe108000000000002, rule => qr"^$pred?IMNMX$u32$hilo $r0cc, $r8, $cr20, $p39;"o,                  },
    #{ 0x0100000000000001ull, 0x37c0000000000003ull, T(minmax), T(us32_33), DST, SRC1, T(i3bi2) }
    { type => $shftT,  code => 0xc108000000000001, rule => qr"^$pred?IMNMX$u32$hilo $r0cc, $r8, $i20, $p39;"o,                  },
    ],
    #{ 0x1a80000000000002ull, 0x3f80000000000003ull, N("set"), N("b32"), DST, T(isetit), T(us32_33), SRC1, T(is2), T(setlop) }
    #Note:default is s32, according to T(us32_33), we should set 51 bit to be 1
    ISET      => [
    #{ 0x1a80000000000002ull, 0x3f80000000000003ull, N("set"), N("b32"), DST, T(acout32), T(isetit), T(us32_33), SRC1, T(is2), T(setlop3) }
    { type => $shftT,  code => 0xda88000000000002, rule => qr"^$pred?ISET$bf$icmp$u32$X$bool$S $r0, $r8, $cr20, $p39;"o,       },
    #{ 0xb280000000000001ull, 0xb780000000000003ull, N("set"), N("b32"), DST, T(acout32), T(isetit), T(us32_33), SRC1, I3BIMM, T(setlop3) }
    { type => $shftT,  code => 0xb288000000000001, rule => qr"^$pred?ISET$bf$icmp$u32$X$bool$S $r0, $r8, $i20, $p39;"o,       },
    ],
    ISETP     => [
    #{ 0x1b00000000000002ull, 0x3f80000000000003ull, N("set"), PDST, PDSTN, T(isetit), T(us32_33), SRC1, T(is2), T(acin2e), T(setlop3) }
    { type => $cmpT,   code => 0xdb08000000000002, rule => qr"^$pred?ISETP$icmp$u32$X$bool$S $p3, $p0, $r8, $cr20, $p39;"o, },
    #{ 0xb300000000000001ull, 0xb780000000000003ull, N("set"), N("b32"), PDST, PDSTN, T(isetit), T(us32_33), SRC1, I3BIMM, T(setlop3) }
    { type => $cmpT,   code => 0xb308000000000001, rule => qr"^$pred?ISETP$icmp$u32$X$bool$S $p3, $p0, $r8, $i20, $p39;"o, },
   ],
   #TODO: Kepler does not have ISCADD.X after I tried all the undetermined bits
    ISCADD    => [
    #{ type => $shftT,  code => 0xc0c0000000000001, rule => qr"^$pred?ISCADD $r0, $r8, $icr20, $i39w8;"o,                   }
    #{ 0x20c0000000000002ull, 0x3fc0000000000003ull, T(addop), N("b32"), DST, N("shl"), SRC1, SHCNT, T(is2) }
    #dst, src1, src2/c[][], scnt
    { type => $shftT,  code => 0xe0c0000000000002, rule => qr"^$pred?ISCADD$X $r0cc, $r8, $cr20, $i39w8;"o,                   },
    #{ 0x00c0000000000001ull, 0x37c0000000000003ull, T(addop), N("b32"), DST, N("shl"), SRC1, SHCNT, T(i3bi2)}
    #immediate: dst, src1, shcnt, i3bimmoff
    { type => $shftT,  code => 0xc0c0000000000001, rule => qr"^$pred?ISCADD$X $r0cc, $r8, $i20, $i39w8;"o,                   }
    ],
    ISCADD32I => [ { type => $shftT,  code => 0x1400000000000000, rule => qr"^$pred?ISCADD32I $r0, $r8, $i20w32, $i53w5;"o,               } ],
#    LEA       => [
#                   { type => $cmpT,   code => 0x5bd0000000000000, rule => qr"^$pred?LEA $p48, $r0cc, $r8, $icr20;"o,                      },
#                   { type => $shftT,  code => 0x5bd7000000000000, rule => qr"^$pred?LEA $r0cc, $r8, $icr20, $i39w8;"o,                    },
#                   { type => $shftT,  code => 0x5bdf004000000000, rule => qr"^$pred?LEA\.HI$X $r0cc, $r8, $r20, $r39, $i28w8;"o,          },
#                   { type => $shftT,  code => 0x0a07000000000000, rule => qr"^$pred?LEA\.HI$X $r0cc, $r8, $c20, $r39, $i51w5;"o,          },
#                 ],

    #INV1:not2a INV:not2b
    LOP       => [
    #{ 0x2200000000000002ull, 0x3fc0000000000003ull, T(logop), N("b32"), DST, T(not2a), SRC1, T(not2b), T(is2) }
    { type => $x32T,   code => 0xe200000000000002, rule => qr"^$pred?LOP$bool$S $r0, (?<INV1>~)?$r8, (?<INV>~)?$cr20(?<INV>\.INV)?;"o, },
    #{ 0x0200000000000001ull, 0x37c0000000000003ull, T(logop), N("b32"), DST, T(not3a),     SRC1, T(not3b), T(i3bi2) }
    { type => $x32T,   code => 0xc200000000000001, rule => qr"^$pred?LOP$bool$S $r0, (?<INV1>~)?$r8, (?<INV>~)?$i20(?<INV>\.INV)?;"o, },
    ],
    #0x2000000000000000ull, 0xfc80000000000000ull
    LOP32I    => [ { type => $x32T,   code => 0x2000000000000000, rule => qr"^$pred?LOP32I$bool $r0, $r8, $i20w32;"o,                     } ],
    LOP3      => [
                   { type => $x32T,   code => 0x5be7000000000000, rule => qr"^$pred?LOP3\.LUT $r0, $r8, $r20, $r39, $i28w8;"o,            },
                   { type => $x32T,   code => 0x3c00000000000000, rule => qr"^$pred?LOP3\.LUT $r0, $r8, $i20, $r39, $i48w8;"o,            },
                 ],
    POPC      => [
    #{ 0x2040000000000002ull, 0x3fc0000000000003ull, N("popc"), N("b32"), DST, T(not2a), SRC1, T(not2b), T(is2) }
    { type => $s2rT,   code => 0xe040000000000002, rule => qr"^$pred?POPC $r0, $r8, $cr20;"o,                                    },
    #{ 0x0040000000000001ull, 0x37c0000000000003ull, N("popc"), N("b32"), DST, T(not2a), SRC1, T(i3bi2) }
    { type => $s2rT,   code => 0xc040000000000001, rule => qr"^$pred?POPC $r0, $r8, $i20;"o,                                    },
    ],
    SHF       => [
    #old { 0x1fc0000000000002ull, 0x3fc0000000000003ull, N("lshf"), N("b32"), DST, SESTART, N("b64"),SRC1, SRC3, SEEND, T(shfclamp), T(is2) }
    #new { 0xdfc0000000000002ull, 0xffc0000000000003ull, N("lshf"), N("b32"), DST, SESTART, N("b64"),SRC1, SRC3, SEEND, T(shfclamp), SRC2 }
    #diff: second src operand
    #flag: shfclamp: .W
                   { type => $shftT,  code => 0xdfc0000000000002, rule => qr"^$pred?SHF\.L$shf $r0, $r8, $r20, $r39;"o,                  },
                   { type => $shftT,  code => 0xb7c0000000000001, rule => qr"^$pred?SHF\.L$shf $r0, $r8, $i20, $r39;"o,                  },
                   #{ 0x27c0000000000002ull, 0x3fc0000000000003ull, N("rshf"), N("b32"), DST, SESTART, T(us64_28), SRC1, SRC3, SEEND, T(shfclamp), T(is2) }
                   { type => $shftT,  code => 0xe7c0000000000002, rule => qr"^$pred?SHF\.R$shf $r0, $r8, $r20, $r39;"o,                  },
                   #{ 0x07c0000000000001ull, 0x37c0000000000003ull, N("rshf"), N("b32"), DST, SESTART, T(us64_28), SRC1, SRC3, SEEND, T(shfclamp), T(sui2b) }
                   { type => $shftT,  code => 0xc7c0000000000001, rule => qr"^$pred?SHF\.R$shf $r0, $r8, $i20, $r39;"o,                  },
                 ],
    SHL       => [
    #{ 0x2240000000000002ull, 0x3fc0000000000003ull, N("shl"), N("b32"), DST, SRC1, T(shclamp), T(is2) }
    { type => $shftT,  code => 0xe240000000000002, rule => qr"^$pred?SHL(?<W>\.W)? $r0, $r8, $cr20;"o,                    },
    #{ 0x0240000000000001ull, 0x37c0000000000003ull, N("shl"), N("b32"), DST, SRC1, T(shclamp), T(sui2b) }
    { type => $shftT,  code => 0xc240000000000001, rule => qr"^$pred?SHL(?<W>\.W)? $r0, $r8, $i23w6;"o,                    },
    ],
    SHR       => [
    #{ 0x2148000000000002ull, 0x3fc8000000000003ull, N("shr"), N("s32"), DST, SRC1, T(is2) }
    #new envy:{ 0x2140000000000002ull, 0x3fc0000000000003ull, N("shr"), T(us32_33), DST, SRC1, T(shclamp), T(is2) }
    { type => $shftT,  code => 0xe148000000000002, rule => qr"^$pred?SHR$u32$W $r0, $r8, $cr20;"o,                          },
    #{ 0x0140000000000001ull, 0x37c0000000000003ull, N("shr"), T(us32_33), DST, SRC1, T(shclamp), T(sui2b) }
    { type => $shftT,  code => 0xc148000000000001, rule => qr"^$pred?SHR$u32$W $r0, $r8, $i23w6;"o,                          },
   ],
#XMAD      => [
#                   { type => $x32T,   code => 0x5b00000000000000, rule => qr"^$pred?XMAD$xmad $r0cc, $r8, $ir20, $r39;"o,                 },
#                   { type => $x32T,   code => 0x5900000000000000, rule => qr"^$pred?XMAD$xmad $r0cc, $r8, $r39s20, $c20s39;"o,            },
#                   { type => $x32T,   code => 0x5e00000000000000, rule => qr"^$pred?XMAD$xmadc $r0cc, $r8, $c20x, $r39;"o,                  },
#                 ],
IMAD      => [
    #{ 0x1000000000000002ull, 0x3c00000000000003ull, T(addop3a), T(sat35), DST, T(acout32), SESTART, N("mul"), T(high39),      T(us32_33), SRC1, T(us32_38), T(is2w3), SEEND, T(is3), T(acin34) }
                    #IMAD DST, SRC1, SRC2, SCR3  63~62 11, 63~59 1101
                    #flag: acin34 CC acout32
                    #default type is S32
                   { type => $x32T,   code => 0xd108000000000002, rule => qr"^$pred?IMAD$imad$hi$X$S $r0cc, $r8, $r20, $r39;"o,                 },
                    #IMAD DST, SRC1, SRC3, c[][] :opcode is 10
                   { type => $x32T,   code => 0xd108000000000002, rule => qr"^$pred?IMAD$imad$hi$X$S $r0cc, $r8, $r39s20, $c20s39;"o,            },
                    #IMAD DST, SRC1, c[][], SRC3: opcode is 01
                   { type => $x32T,   code => 0xd108000000000002, rule => qr"^$pred?IMAD$imad$hi$X$S $r0cc, $r8, $c20x, $r39;"o,                  },
                   #{ 0xa000000000000001ull, 0xb400000000000003ull, T(addop3a), T(sat39), DST, SESTART, N("mul"), T(us32_33), SRC1, T(us32_38), I3BIMM, SEEND, SRC3 },
                   { type => $x32T,   code => 0xa108000000000001, rule => qr"^$pred?IMAD$imad$hi$X$S $r0cc, $r8, $i20, $r39;"o,                  },
                 ],
    #IMAD  => [ { type => $x32T,  code => 0xd000000000000002, rule => qr"^$pred?IMAD$hi$X $r0cc, $r8, $icr20, $icr20;"o,            } ],
    IMADSP    => [ { type => $x32T,   code => 0x0000000000000000, rule => qr"^$pred?IMADSP[^;]*;"o, } ], #TODO
    IMUL      => [
    #default is S32
    #{ 0x21c0000000000002ull, 0x3fc0000000000003ull, N("mul"), T(high2a), DST, T(acout32), T(us32_2b), SRC1, T(us32_2c), T(is2) }, // XXX: order of us32
    { type => $x32T,   code => 0xe1c0180000000002, rule => qr"^$pred?IMUL$imul$hi $r0, $r8, $cr20;"o,   },
    #{ 0x01c0000000000001ull, 0x37c0000000000003ull, N("mul"), T(high2a), DST, T(us32_2b), SRC1, T(us32_2c), T(i3bi2) }
    { type => $x32T,   code => 0xc1c0180000000001, rule => qr"^$pred?IMUL$imul$hi $r0, $r8, $i20;"o,   },
    ],
    IMUL32I      => [
    #default is S32
    #{ 0x2800000000000002ull, 0xf880000000000003ull, N("mul"), T(high38), DST, T(us32_39), SRC1, T(us32_3a), LIMM }
    { type => $x32T,   code => 0x2e00000000000002, rule => qr"^$pred?IMUL32I$imul$hi $r0, $r8, $i20w32;"o,   },
    ],

    #Conversion Instructions
    #F2F.F32.F32
    #{ 0x2540000000002802ull, 0x3fc0000000003c03ull, N("cvt"), T(ftz2f), T(sat35), T(rint), N("f32"), DST, N("f32"), T(neg30), T(abs34), T(is2) }
    #F2F.F64.F32
    #{ 0x2540000000002c02ull, 0x3fc0000000003c03ull, N("cvt"), N("f64"), DST, N("f32"), T(neg30), T(abs34), T(is2) }
    #F2F.F32.F64
    #{ 0x2540000000003802ull, 0x3fc0000000003c03ull, N("cvt"), T(frm2a), N("f32"), DST, N("f64"), T(neg30), T(abs34), T(is2) }
    #F2F.F64.F64
    #{ 0x2540000000003c02ull, 0x3fc0000000003c03ull, N("cvt"), T(rint), N("f64"), DST, N("f64"), T(neg30), T(abs34), T(ds2) }
    F2F => [ { type => $qtrT,  code => 0xe540000000000002, rule => qr"^$pred?F2F$ftz$x2x$rnd$round$sat $r0, $cr20;"o, } ],
    #{ 0x2580000000000002ull, 0x3fc0000000000003ull, N("cvt"), T(ftz2f), T(frmi), T(cvtf2idst), T(neg30), T(abs34), T(cvtf2isrc) }
    #is2 or ds2
    F2I => [ { type => $qtrT,  code => 0xe580000000000002, rule => qr"^$pred?F2I$ftz$x2x$round $r0, $cr20;"o,         } ],
    #{ 0x25c0000000000002ull, 0x3fc0000000000003ull, N("cvt"), T(frm2a), T(cvti2fdst), T(neg30), T(abs34), T(cvti2fsrc) }
    I2F => [ { type => $qtrT,  code => 0xe5c0000000000002, rule => qr"^$pred?I2F$x2x$rnd $r0, $cr20;"o,               } ],
    #{ 0x2600000000000002ull, 0x3fc0000000000003ull, N("cvt"), T(sat35), T(cvti2idst), T(neg30), T(abs34), T(cvti2isrc) }
    I2I => [ { type => $qtrT,  code => 0xe600000000000002, rule => qr"^$pred?I2I$x2x$sat $r0, $cr20;"o,               } ],
    F2ITRUNC => [ { type => $qtrT,  code => 0xe5800c00051ca846, rule => qr"^$pred?F2ITRUNC[^;]*;"o,               } ],

    #Movement Instructions
    #{ 0x24c0000000000002ull, 0x3fc0000000000003ull, T(lane2a), N("mov"), N("b32"), DST, T(is2) }
    #MOV    => [ { type => $x32T,  code => 0xe4c03c0000000002, rule => qr"^$pred?MOV $r0, $icr20;"o,                   } ],
    MOV    => [ { type => $x32T,  code => 0xe4c03c0000000002, rule => qr"^$pred?MOV$lane2a$S $r0, $cr20;"o,                   } ],
    #{ 0x7400000000000002ull, 0x7f80000000000003ull, T(lane0e), N("mov"), N("b32"), DST, LIMM }
    MOV32I => [ { type => $x32T,  code => 0x740000000003c002, rule => qr"^$pred?MOV32I$lane0e$S $r0, (?:$i20w32|$f20w32);"o,   } ],
    PRMT   => [
    #{ 0xde00000000000002ull, 0xffc0000000000003ull, N("prmt"), T(prmtmod), N("b32"), DST, SRC1, SRC3, SRC2}
    { type => $x32T,  code => 0xde00000000000002, rule => qr"^$pred?PRMT$prmt $r0, $r8, $cr20, $cr39;"o, },
    #{ 0xb600000000000001ull, 0xb7c0000000000003ull, N("prmt"), T(prmtmod), N("b32"), DST, SRC1, SRC3, I3BIMM}
    { type => $x32T,  code => 0xb600000000000001, rule => qr"^$pred?PRMT$prmt $r0, $r8, $i20, $r39;"o, },
    ],
    SEL    => [
    #{ 0x2500000000000002ull, 0x3fc0000000000003ull, N("selp"), N("b32"), DST, SRC1, T(is2), T(pnot2d), PSRC3 }
    { type => $x32T,  code => 0xe500000000000002, rule => qr"^$pred?SEL $r0, $r8, $cr20, $p39;"o,        },
    #{ 0x0500000000000001ull, 0x37c0000000000003ull, N("selp"), DST, SRC1, T(i3bi2), T(pnot2d), PSRC3 }
    { type => $x32T,  code => 0xc500000000000001, rule => qr"^$pred?SEL $r0, $r8, $i20, $p39;"o,        },
    ],
    # { 0x7880000000000002ull, 0x7fc0000000000003ull, N("shfl"), T(shflmod), N("b32"), DST, PDST2, SRC1, T(sflane), T(sfmask)}
    #0x0000000080000000 31  F(sflane,   0x1f,SRC2,SFLNIMM)
    #0x0000000100000000 32  F(sfmask,   0x20,SRC3,SFLMIMM)
    SHFL   => [ { type => $smemT, code => 0x7880000000000002, rule => qr"^$pred?SHFL$shfl $p48, $r0, $r8, (?:$i20w8|$r20), (?:$i34w13|$r39);"o, } ],

    #Predicate/CC Instructions
    #{ 0x8440000000000002ull, 0xffc0000000000003ull, N("set"), DST, T(acout32), T(pnot11), PSRC1, T(setlop2), T(setlop3) }
    PSET   => [ { type => $cmpT,  code => 0x8440000000000002, rule => qr"^$pred?PSET$bf$bool2$bool $r0, $p12, $p29, $p39;"o,       } ],
    #{ 0x8480000000000002ull, 0xffc0000000000003ull, N("set"), PDST, PDSTN, T(pnot11), PSRC1, T(setlop2), T(setlop3)}
    PSETP  => [ { type => $cmpT,  code => 0x8480000000000002, rule => qr"^$pred?PSETP$bool2$bool$S $p3, $p0, $p12, $p29, $p39;"o, } ],
    CSET   => [ { type => $x32T,  code => 0x0000000000000000, rule => qr"^$pred?CSET[^;]*;"o,  } ], #TODO
    CSETP  => [ { type => $x32T,  code => 0x0000000000000000, rule => qr"^$pred?CSETP[^;]*;"o, } ], #TODO
    P2R    => [ { type => $x32T,  code => 0x38e8000000000000, rule => qr"^$pred?P2R $r0, PR, $r8, $i20w7;"o,   } ],
    R2P    => [ { type => $cmpT,  code => 0x38f0000000000000, rule => qr"^$pred?R2P PR, $r8, $i20w7;"o,   } ],

    #Texture Instructions
    # Handle the commonly used 1D texture functions.. but save the others for later
    #{ 0x7000000000000002ull, 0x7c00000000000003ull, N("texfetch"), T(texm), T(lodf), T(texms), T(texoff2),     T(ltex), TDST, T(text), T(texsrc1), T(texsrc2) }
    #TLD    => [ { type => $gmemT, code => 0x7000003d379fff22, rule => qr"^$pred?TLD[^;]*;"o, } ], #Partial
    #TLD.LZ.P R0, RZ, 0x52, 1D, 0x1;
    TLD    => [ { type => $gmemT, code => 0x700a00067f9ffc02, rule => qr"^$pred?TLD[^;]*;"o, } ], #Partial
    TLDzxx    => [ { type => $gmemT, code => 0x700a00057f9ffc02, rule => qr"^$pred?TLDzxx[^;]*;"o, } ], #Partial
    #TEXDEPBAR    => [ { type => $gmemT, code => 0x77000000001c0002, rule => qr"^$pred?TEXDEPBAR[^;]*;"o, } ], #Partial
    TEXDEPBAR    => [ { type => $gmemT, code => 0x77000000001c0002, rule => qr"^$pred?TEXDEPBAR $i20w6;"o, } ], #Partial
    #TEXDEPBARzxx    => [ { type => $gmemT, code => 0x770000003f9c0002, rule => qr"^$pred?TEXDEPBARzxx[^;]*;"o, } ], #Partial
    #TEXDEPBAR    => [ { type => $gmemT, code => 0x77000000001c0002, rule => qr"^$pred?TEXDEPBAR[^;]*;"o, } ], #Partial
    #TLD    => [ { type => $gmemT, code => 0x7000000000000002, rule => qr"^$pred?TLD\.LZ\.$tld $r0, $r8, $r20, $hex, \dD, $i31w4;"o, } ], #Partial
    #TLD    => [ { type => $gmemT, code => 0x7000000000000002, rule => qr"^$pred?TLD\.B\.LZ\.$tld $r0, $r8, $r20, $hex, \dD, $i31w4;"o, } ], #Partial
    #TLDS   => [ { type => $gmemT, code => 0xda0000000ff00000, rule => qr"^$pred?TLDS\.LZ\.$tld $r28, $r0, $r8, $i36w20, \dD, $chnls;"o,} ], #Partial
    TEX    => [ { type => $gmemT, code => 0x0000000000000000, rule => qr"^$pred?TEX[^;]*;"o,   } ], #TODO
    TLD4   => [ { type => $gmemT, code => 0x0000000000000000, rule => qr"^$pred?TLD4[^;]*;"o,  } ], #TODO
    TXQ    => [ { type => $gmemT, code => 0x0000000000000000, rule => qr"^$pred?TXQ[^;]*;"o,   } ], #TODO
    #TEXS   => [ { type => $gmemT, code => 0x0000000000000000, rule => qr"^$pred?TEXS[^;]*;"o,  } ], #TODO
    #TLD4S  => [ { type => $gmemT, code => 0x0000000000000000, rule => qr"^$pred?TLD4S[^;]*;"o, } ], #TODO

    #Compute Load/Store Instructions
    #0xc000000000000000ull, 0xe000000000000000ull T(p), N("ld"), T(ldstt), T(ldstd), T(lcop),T(gmem)
    #Bit 55 is .E flag
    LD     => [ { type => $gmemT, code => 0xc000000000000000, rule => qr"^$pred?LD$memCache$memType $r0, $addr;"o,      } ],
    #{ 0x7f80000000000002ull, 0x7fc0000000000003ull, N("ld"), N("b32"), DST, VBA },
    # VILD(LDY)
    LDY     => [ { type => $gmemT, code => 0x7f80000000000002, rule => qr"^$pred?LDY $r0, $i20;"o,      } ],
    #{ 0x7ec0000000000002ull, 0x7fc0000000000003ull, N("ld"), T(patch), T(aldstt), T    (aldstd), T(outa), ATTR, SRC1, SRC3 },
    # ALD(LDX)
    LDX     => [ { type => $gmemT, code => 0x7ec0000000000002, rule => qr"^$pred?LDX$memTypeX $r0, $addr;"o,      } ],
    #0xe000000000000000ull, 0xe000000000000000ull, T(p), N("st"), T(ldstt), T(scop), T(gmem), T(ldstd)
    ST     => [ { type => $gmemT, code => 0xe000000000000000, rule => qr"^$pred?ST$memCache$memType $addr, $r0;"o,      } ],
    #LDG load by texture cache
    #can not have offset in source operand, eg [R0+0x16] is not supported in Kepler, use TLD instead when have offset
    #{ 0x7000000000000002ull, 0x7c00000000000003ull, N("texfetch"), T(texm), T(lodf), T(texms), T(texoff2), T(ltex), TDST, T(text), T(texsrc1), T(texsrc2) }
    #$addr  = qr"\[(?:(?<r8>$reg)|(?<nor8>))(?:\s*\+?\s*$i20w24)?\]"o;
    LDG    => [
    #.E 0x0000008....
    { type => $gmemT, code => 0x600010047f800001, rule => qr"^$pred?LDG$memCache$memType $r0, $addr;"o,           },
    ],
    #STG    => [ { type => $gmemT, code => 0xeed8000000000000, rule => qr"^$pred?STG$memCache$memType $addr, $r0;"o,           } ],
    # 0x7a40000000000002ull, 0x7fc0000000000003ull, N("ld"), T(lldstt), T(lldstd), SHARED
    #.U only be effective to 128 bit load: LDS.U.128
    LDS    => [ { type => $smemT, code => 0x7a40000000000002, rule => qr"^$pred?LDS$memCache$memType$S $r0, $addr;"o,           } ],
    #{ 0x7ac0000000000002ull, 0x7fc0000000000003ull, N("st"), T(lldstt), SHARED, T(lldstd) }
    #$addr  = qr"\[(?:(?<r8>$reg)|(?<nor8>))(?:\s*\+?\s*$i20w24)?\]"o;
    STS    => [ { type => $smemT, code => 0x7ac0000000000002, rule => qr"^$pred?STS$memCache$memType$S $addr, $r0;"o,           } ],
    #{0x7a00000000000002ull, 0x7fc0000000000003ull, N("ld"), T(lldstt), T(llcop), T(lldstd), LOCAL}
    LDL    => [ { type => $gmemT, code => 0x7a00000000000002, rule => qr"^$pred?LDL$ldmemCache$memType$S $r0, $addr;"o,           } ],
    #{ 0x7a80000000000002ull, 0x7fc0000000000003ull, N("st"), T(lldstt), T(lscop), LOCAL, T(lldstd)}
    STL    => [ { type => $gmemT, code => 0x7a80000000000002, rule => qr"^$pred?STL$stmemCache$memType$S $addr, $r0;"o,           } ],
    #{ 0x7c80000000000002ull, 0x7fc0000000000003ull, N("ld"), T(lldstt), T(lldstd), LCONST }
    LDC    => [ { type => $gmemT, code => 0x7c800000000ffc02, rule => qr"^$pred?LDC$memCache$memType$S $r0, $ldc;"o,            } ],
    # Note for ATOM(S).CAS operations the last register needs to be in sequence with the second to last (as it's not encoded).
    ATOM   => [ { type => $gmemT, code => 0xed00000000000000, rule => qr"^$pred?ATOM$atom $r0, $addr2, $r20(?:, $r39a)?;"o,   } ],
    #ATOMS  => [ { type => $smemT, code => 0xec00000000000000, rule => qr"^$pred?ATOMS$atom $r0, $addr2, $r20(?:, $r39a)?;"o,  } ],
    #$atom  = qr"(?<E>\.E)?(?:\.(?<mode>ADD|MIN|MAX|INC|DEC|AND|OR|XOR|EXCH|CAS))(?<type>|\.S32|\.U64|\.F(?:16x2|32)\.FTZ\.RN|\.S64|\.64)";
    #RED.E
    #{ 0x6800000000000002ull, 0xf800000000000003ull, N("ld"), T(redop), T(atomd), T(gamem), T(atoms) }
    #RED donot have EXCH nor SAFEADD flag, which is different from tabredop
    #since We donot use dst register, we set dst register to RZ(bit 2~9 is all ones)
    RED    => [ { type => $gmemT, code => 0x68000000000003fe, rule => qr"^$pred?RED$atom $addr2, $r20;"o,                      } ],
    CCTL   => [ { type => $x32T,  code => 0x5c88000000000000, rule => qr"^$pred?CCTL[^;]*;"o,  } ], #TODO
    CCTLL  => [ { type => $x32T,  code => 0x5c88000000000000, rule => qr"^$pred?CCTLL[^;]*;"o, } ], #TODO
    #CCTLT  => [ { type => $x32T,  code => 0x5c88000000000000, rule => qr"^$pred?CCTLT[^;]*;"o, } ], #TODO

    #Surface Memory Instructions (haven't gotten to these yet..)
    #SUATOM => [ { type => $x32T, code => 0x0000000000000000, rule => qr"^$pred?SUATOM[^;]*;"o, } ], #TODO
    SULD   => [ { type => $x32T, code => 0x0000000000000000, rule => qr"^$pred?SULD[^;]*;"o,   } ], #TODO
    #SURED  => [ { type => $x32T, code => 0x0000000000000000, rule => qr"^$pred?SURED[^;]*;"o,  } ], #TODO
    #SUST   => [ { type => $x32T, code => 0x0000000000000000, rule => qr"^$pred?SUST[^;]*;"o,   } ], #TODO

    #Control Instructions
    BRA    => [
                #relative jump
                #{ 0x1200000000000000ull, 0xff80000000000000ull, T(p), T(cc), N("bra"), T(lim),T(brawarp), BTARG }
                { type => $x32T, code => 0x120000000000003c, rule => qr"^$pred?BRA(?<U>\.U)? $i20w24;"o,         },
                { type => $x32T, code => 0x1200000000000000, rule => qr"^$pred?BRA(?<U>\.U)? CC\.$condition, $i20w24;"o,         },
              ],

    BRX    => [ { type => $x32T, code => 0x0000000000000000, rule => qr"^$pred?BRX[^;]*;"o,                      } ], #TODO
    #{ 0x1080000000000000ull, 0xff80000000000000ull, T(p), T(cc), N("bra"), T(lim),T(brawarp), N("abs"), ACTARG }
    #Jump to Absolute Address
    JMP    => [
    { type => $x32T, code => 0x108000000000003c, rule => qr"^$pred?JMP(?<U>\.U)? $i20w32;"o,         },
    { type => $x32T, code => 0x1080000000000000, rule => qr"^$pred?JMP(?<U>\.U)? CC\.$condition, $i20w32;"o,         },
    ],
    JMX    => [ { type => $x32T, code => 0x0000000000000000, rule => qr"^$pred?JMX[^;]*;"o,                      } ], #TODO
    #{ 0x1480000000000000ull, 0xff80000000000000ull, N("joinat"), BTARG }
    SSY    => [ { type => $x32T, code => 0x1480000000000000, rule => qr"^$noPred?SSY $i20w24;"o,                 } ],
    #SYNC   => [ { type => $x32T, code => 0xf0f800000000000f, rule => qr"^$pred?SYNC;"o,                          } ],

    #{ 0x1300000000000000ull, 0xff80000000000000ull, N("call"), T(lim), CTARG }
    #Bit 8 default is 1
    CAL    => [ { type => $x32T, code => 0x1300000000000100, rule => qr"^$noPred?CAL $i20w24;"o,                 } ],
    #{ 0x1100000000000000ull, 0xff80000000000000ull, N("call"), T(lim), N("abs"), ACTARG }
    #Bit 8: T(lim) default 1
    JCAL   => [ { type => $x32T, code => 0x1100000000000100, rule => qr"^$noPred?JCAL $i20w32;"o,                } ],
    #JCAL c[0x0][0x170];
    #JCALX   => [ { type => $x32T, code => 0x1100000000000100, rule => qr"^$noPred?JCALX $z20;"o,                } ],
    PRET   => [ { type => $x32T, code => 0x0000000000000000, rule => qr"^$pred?PRET[^;]*;"o,                     } ], #TODO
    #{ 0x1900000000000000ull, 0xff80000000000000ull, T(p), T(cc), N("ret") }
    RET    => [
    { type => $x32T, code => 0x190000000000003c, rule => qr"^$pred?RET;"o,                           },
    { type => $x32T, code => 0x1900000000000000, rule => qr"^$pred?RET CC\.$condition;"o,                           },
    ],
    #rule @P0 BRK;
    BRK    => [ { type => $x32T, code => 0x1a0000000000003c, rule => qr"^$pred?BRK;"o,                           } ],
    #{ 0x1500000000000000ull, 0xff80000000000000ull, N("prebrk"), BTARG }
    PBK    => [ { type => $x32T, code => 0x1500000000000000, rule => qr"^$noPred?PBK $i20w24;"o,                 } ],
    CONT   => [ { type => $x32T, code => 0xe35000000000000f, rule => qr"^$pred?CONT;"o,                          } ],
    PCNT   => [ { type => $x32T, code => 0xe2b0000000000000, rule => qr"^$noPred?PCNT $i20w24;"o,                } ],
    #{ 0x1800000000000000ull, 0xff80000000000000ull, T(p), T(cc), N("exit") }
    EXIT   => [
    { type => $x32T, code => 0x18000000001c003c, rule => qr"^$pred?EXIT;"o,                          },
    { type => $x32T, code => 0x18000000001c0000, rule => qr"^$pred?EXIT CC\.$condition;"o,                          },
    ],
    #PEXIT  => [ { type => $x32T, code => 0x0000000000000000, rule => qr"^$pred?PEXIT[^;]*;"o,                    } ], #TODO
    BPT    => [ { type => $x32T, code => 0xe3a00000000000c0, rule => qr"^$noPred?BPT\.TRAP $i20w24;"o,           } ],

    #Miscellaneous Instructions
    #0x85800000001c3c02
    #0x8580000000003c02
    NOP    => [ { type => $x32T,  code => 0x8580000000003c02, rule => qr"^$pred?NOP$S;"o,                                     } ],
    #CS2R   => [ { type => $x32T,  code => 0x50c8000000000000, rule => qr"^$pred?CS2R $r0, $sr;"o,                           } ],
    #{ 0x8640000000000002ull, 0xbfc0000000000003ull, N("mov"), N("b32"), DST, SREG }
    S2R    => [ { type => $s2rT,  code => 0x8640000000000002, rule => qr"^$pred?S2R$S $r0, $sr;"o,                            } ],
    B2R    => [ { type => $x32T,  code => 0xf0b800010000ff00, rule => qr"^$pred?B2R$b2r;"o,                                 } ],
    #{ 0x0540000800000002ull, 0x3fc0000800000003ull, N("bar"), N("arrive"), BAR, OOPS}
    BAR    => [
    #BAR.SYNC a, {b}
    #$bar   = qr"\.(?<mode>SYNC|ARV|RED)(?:\.(?<red>POPC|AND|OR))? (?:$i8w4|$r8)(?:, (?:$i20w12|$r20))?(?(<r20>)|(?<nor20>))(?(<red>), $p39|(?<nop39>))"o;
    { type => $gmemT, code => 0x8540dc0000000002, rule => qr"^$pred?BAR.SYNC $i8w4;"o,                                 },
    { type => $gmemT, code => 0x8540dc0000000002, rule => qr"^$pred?BAR.SYNC $i8w4, $i20w12;"o,                                 },
    { type => $gmemT, code => 0x85409c0000000002, rule => qr"^$pred?BAR.SYNC $i8w4, $r20;"o,                                 },
    { type => $gmemT, code => 0x85405c0000000002, rule => qr"^$pred?BAR.SYNC $r8;"o,                                 },
    { type => $gmemT, code => 0x85405c0000000002, rule => qr"^$pred?BAR.SYNC $r8, $i20w12;"o,                                 },
    { type => $gmemT, code => 0x85401c0000000002, rule => qr"^$pred?BAR.SYNC $r8, $r20;"o,                                 },
    { type => $gmemT, code => 0x8540dc0800000002, rule => qr"^$pred?BAR.ARV $i8w4, $i20w12;"o,                                 },
    { type => $gmemT, code => 0x85409c0800000002, rule => qr"^$pred?BAR.ARV $i8w4, $r20;"o,                                 },
    { type => $gmemT, code => 0x85405c0800000002, rule => qr"^$pred?BAR.ARV $r8, $i20w12;"o,                                 },
    { type => $gmemT, code => 0x85401c0800000002, rule => qr"^$pred?BAR.ARV $r8, $r20;"o,                                 },
    ],
    DEPBAR => [
                { type => $gmemT, code => 0xf0f0000000000000, rule => qr"^$pred?DEPBAR$icmp $dbar, $i20w6;"o, },
                { type => $gmemT, code => 0xf0f0000000000000, rule => qr"^$pred?DEPBAR$dbar2;"o,              },
              ],
    MEMBAR => [ { type => $x32T,  code => 0xef98000000000000, rule => qr"^$pred?MEMBAR$mbar;"o,                             } ],
    #VOTE.ALL { 0x86c0000000000002ull, 0xfff8000000000003ull, N("vote"), N("all"), DST, PSRC4, PSRC3 },
    #VOTE.ANY { 0x86c8000000000002ull, 0xfff8000000000003ull, N("vote"), N("any"), DST, PSRC4, PSRC3 },
    #VOTE.EQ { 0x86d0000000000002ull, 0xfff8000000000003ull, N("vote"), N("uni"), DST, PSRC4, PSRC3 },
    #VOTE   => [
    #{ type => $voteT, code => 0x86c0000000000002, rule => qr"^$pred?VOTE$vote $r0, $p45, $p39;"o, },
    #{ type => $voteT, code => 0x86c00000000003fe, rule => qr"^$pred?VOTE$vote $p45, $p39;"o, },
    #],

    # (?:$r0, |(?<nor0>)) meaning: with r0, or just capture <nor0> without r0
    VOTE   => [
    { type => $voteT, code => 0x86c0000000000002, rule => qr"^$pred?VOTE$vote (?:$r0, |(?<nor0>))$p45, $p39;"o, } ],

    #R2B    => [ { type => $x32T,  code => 0x0000000000000000, rule => qr"^$pred?R2B[^;]*;"o,                                } ], #TODO

    #Video Instructions... Need to finish
    VADD   => [   { type => $shftT, code => 0x2044000000000000, rule => qr"^$pred?VADD$vaddType$sat$vaddMode $r0, $r8, $r20, $r39;"o, } ], #Partial 0x2044000000000000
    VMAD   => [
                  { type => $x32T,  code => 0xf800000000000002, rule => qr"^$pred?VMAD$vmad16 $r0, $r8, $i20, $r39;"o, },
                  { type => $x32T,  code => 0xf800000000000002, rule => qr"^$pred?VMAD$vmad16 $r0, $r8, $r20, $r39;"o, },
                  { type => $shftT, code => 0xf800000000000002, rule => qr"^$pred?VMAD$vmad8 $r0, $r8, $r20, $r39;"o, },
              ],
    VABSDIFF => [ { type => $shftT, code => 0x5427000000000000, rule => qr"^$pred?VABSDIFF$vaddType$sat$vaddMode $r0, $r8, $r20, $r39;"o, } ], #Partial 0x2044000000000000
    VMNMX    => [ { type => $shftT, code => 0x3a44000000000000, rule => qr"^$pred?VMNMX$vaddType$vmnmx$sat$vaddMode $r0, $r8, $r20, $r39;"o, } ], #Partial 0x2044000000000000

    VSET => [ { type => $shftT, code => 0x4004000000000000, rule => qr"^$pred?VSET$icmp$vaddType$vaddMode $r0, $r8, $r20, $r39;"o, } ], #Partial 0x2044000000000000
);

# Create map of capture groups to op code flags that need to be added (or removed)
my @flags = grep /\S/, split "\n", q{;

BFE, BFI, FLO, IADD, ISUB, IADD3, ICMP, IMNMX, ISCADD, ISET, ISETP, LEA, LOP, LOP3, MOV, PRMT, SEL, SHF, SHL, SHR, XMAD
0x0800000000000000 neg

FADD, FCMP, FFMA, FMNMX, FMUL, FSET, FSETP, DADD, DFMA, DMNMX, DMUL, DSET, DSETP
0x0800000000000000 neg

PSET, PSETP
0x0000000000020000 p12not
0x0000000800000000 p29not

FMNMX, FSET, FSETP, DMNMX, DSET, DSETP, IMNMX, ISET, ISETP, SEL, PSET, PSETP, BAR, VOTE
0x0000200000000000 p39not

IADD32I
0x0010000000000000 CC

IMAD, PSET, FSET, DSET, ISET, IADD, ISUB, IMUL, ISCADD
0x0004000000000000 CC

IMAD: mode
0x0200000000000000 HI

IMAD
0x0010000000000000 X

IMUL: mode
0x0000040000000000 HI

IMUL32I: mode
0x0100000000000000 HI

FFMA, FADD, FCMP, FMUL, FMNMX,  FSWZ, FSET, FSETP,  FCHK, RRO,  MUFU, DFMA, DADD, DMUL, DMNMX,  DSET, DSETP,  IMAD, IMADSP, IMUL, IADD, ISCADD, ISAD, IMNMX,  BFE,  BFI,  SHR,  SHL,  SHF,  LOP,  FLO,  ISET, ISETP,  ICMP, POPC, F2F,  F2I,  I2F,  I2I,  MOV, MOV32I, SEL,  PRMT, SHFL, P2R,  R2P,  CSET, CSETP,  PSET, PSETP,  TEX,  TLD,  TLD4, TXQ,  LDC,  LD, LDG,  LDL,  LDS,  LDSLK,  ST, STL,  STS,  STSCUL, ATOM, RED,  CCTL, CCTLL,  MEMBAR, SUCLAMP,  SUBFM,  SUEAU,  SULDGA, SUSTGA, BRA,  BRX,  RET,  BRK,  CONT, NOP,  S2R,  B2R,  BAR,  VOTE, MOV
0x0000000000400000 S

SHF
0x0020000000000000 W
0x0001000000000000 HI

SHF: type
0x0000020000000000 U64
0x0000010000000000 S64

IMAD, ICMP, ISET, ISETP, ISAD, SHR, IMNMX, FLO, BFE
0x0008000000000000 U32

SHR, SHL
0x0000040000000000 W

SHFL
0x0000000080000000 i20w8
0x0000000100000000 i34w13

SHFL: mode
0x0000000000000000 IDX
0x0000000200000000 UP
0x0000000300000000 DOWN
0x0000000600000000 BFLY

IMNMX: mode
0x0000080000000000 XLO
0x0000180000000000 XHI

ISETP, ISET, ICMP: cmp
0x0010000000000000 LT
0x0020000000000000 EQ
0x0030000000000000 LE
0x0040000000000000 GT
0x0050000000000000 NE
0x0060000000000000 GE

ISETP, ISET, PSETP, PSET, FSET, FSETP, DSET, DSETP: bool
0x0000000000000000 AND
0x0001000000000000 OR
0x0002000000000000 XOR

PSETP, PSET: bool2
0x0000000000000000 AND
0x0000000008000000 OR
0x0000000010000000 XOR

ISETP, ISET, IADD, ISUB
0x0000400000000000 X

ISCADD
0x0020000000000000 X

ISET, PSET
0x0000800000000000 BF

LOP: bool
0x0000000000000000 AND
0x0000100000000000 OR
0x0000200000000000 XOR
0x0000300000000000 PASS_B

LOP, POPC, FLO
0x0000080000000000 INV

LOP, POPC, IADD, ISUB
0x0000040000000000 INV1

LOP: z
0x0000200000000000 Z
0x0000300000000000 NZ

LOP
0x0000000000000000 noz

LOP32I: bool
0x0000000000000000 AND
0x0020000000000000 OR
0x0040000000000000 XOR

PRMT: mode
0x0008000000000000 F4E
0x0010000000000000 B4E
0x0018000000000000 RC8
0x0020000000000000 ECL
0x0028000000000000 ECR
0x0030000000000000 RC16

IMAD: type1
0x0008000000000000 U32
0x0008000000000000 S32

IMAD: type2
0x0100000000000000 U32
0x0100000000000000 S32

IMUL: type1
0x0000080000000000 U32
0x0000000000000000 S32

IMUL: type2
0x0000100000000000 U32
0x0000000000000000 S32

IMUL32I: type1
0x0200000000000000 U32
0x0000000000000000 S32

IMUL32I: type2
0x0400000000000000 U32
0x0000000000000000 S32

XMAD: type1
0x0000000000000000 U16
0x0001000000000000 S16

XMAD: type2
0x0000000000000000 U16
0x0002000000000000 S16

XMAD: mode
0x0000002000000000 MRG
0x0000001000000000 PSL
0x0008000000000000 CHI
0x0004000000000000 CLO
0x000c000000000000 CSFU

XMAD: modec
0x0004000000000000 CLO
0x0008000000000000 CHI
0x000c000000000000 CSFU
0x0040000000000000 X
0x0080000000000000 PSL
0x0100000000000000 MRG

XMAD
0x0010000000000000 CBCC

XMAD: r8part
0x0000000000000000 H0
0x0020000000000000 H1

XMAD: r20part
0x0000000000000000 H0
0x0000000800000000 H1

XMAD: r20partx
0x0000000000000000 H0
0x0010000000000000 H1

XMAD: r39part
0x0000000000000000 H0
0x0010000000000000 H1

VMAD, VADD, VABSDIFF, VMNMX, VSET: r8part
0x0000000000000000 B0
0x0000001000000000 B1
0x0000002000000000 B2
0x0000003000000000 B3
0x0000001000000000 H1
0x0000000000000000 H0

VMAD, VADD, VABSDIFF, VMNMX, VSET: r20part
0x0000000000000000 B0
0x0000000010000000 B1
0x0000000020000000 B2
0x0000000030000000 B3
0x0000000010000000 H1
0x0000000000000000 H0

VMAD
0x0040000000000000 r8neg
0x0020000000000000 r39neg
0x0008000000000000 SHR_7
0x0010000000000000 SHR_15
0x0060000000000000 PO
0x0080000000000000 SAT

VMNMX
0x0100000000000000 MX

VADD, VABSDIFF, VMNMX
0x0080000000000000 SAT
0x0040000000000000 UD
0x0040000000000000 SD

VSET: cmp
0x0040000000000000 LT
0x0080000000000000 EQ
0x00c0000000000000 LE
0x0100000000000000 GT
0x0140000000000000 NE
0x0180000000000000 GE

VADD, VSET: mode
0x0020000000000000 ACC
0x0028000000000000 MIN
0x0030000000000000 MAX
0x0000000000000000 MRG_16H
0x0008000000000000 MRG_16L
0x0010000000000000 MRG_8B0
0x0000000000000000 MRG_8B1
0x0018000000000000 MRG_8B2
0x0000000000000000 MRG_8B3

VABSDIFF: mode
0x0003000000000000 ACC
0x000b000000000000 MIN
0x0013000000000000 MAX
0x0023000000000000 MRG_16H
0x002b000000000000 MRG_16L
0x0033000000000000 MRG_8B0
0x0000000000000000 MRG_8B1
0x003b000000000000 MRG_8B2
0x0000000000000000 MRG_8B3

VMNMX: mode
0x0020000000000000 ACC
0x0028000000000000 MIN
0x0030000000000000 MAX
0x0000000000000000 MRG_16H
0x0008000000000000 MRG_16L
0x0010000000000000 MRG_8B0
0x0000000000000000 MRG_8B1
0x0018000000000000 MRG_8B2
0x0000000000000000 MRG_8B3

VMAD, VADD, VABSDIFF, VMNMX, VSET: sign1
0x0000000000000000 U
0x0004000000000000 S

VMAD, VADD, VABSDIFF, VMNMX, VSET: sign2
0x0000000000000000 U
0x0008000000000000 S

VMAD, VADD, VABSDIFF, VMNMX, VSET: size1
0x0000000000000000 8
0x0000004000000000 16
0x0000006000000000 32

VMAD, VADD, VABSDIFF, VMNMX, VSET: size2
0x0000000000000000 8
0x0000000000000000 16
0x0000000000000000 32

IADD3: type
0x0001000000000000 X
0x0000002000000000 RS
0x0000004000000000 LS

IADD3: r8part
0x0000000000000000 H0
0x0000001000000000 H1

IADD3: r20part
0x0000000080000000 H0

IADD3: r39part
0x0000000200000000 H0

IADD3
0x0008000000000000 r8neg
0x0004000000000000 r20neg
0x0002000000000000 r39neg

IADD, ISUB, ISCADD
0x0010000000000000 r8neg
0x0008000000000000 r20neg
0x0018000000000000 PO

IADD32I
0x0100000000000000 X
0x0800000000000000 r8neg

IMAD
0x0080000000000000 r8neg

IMAD
0x0040000000000000 r39neg

DEPBAR: SB
0x0000000000000000 SB0
0x0000000004000000 SB1
0x0000000008000000 SB2
0x000000000c000000 SB3
0x0000000010000000 SB4
0x0000000014000000 SB5

DEPBAR: cmp
0x0000000020000000 LE

DEPBAR
0x0000000000000001 db0
0x0000000000000002 db1
0x0000000000000004 db2
0x0000000000000008 db3
0x0000000000000010 db4
0x0000000000000020 db5

F2F, F2I, I2F, I2I: destWidth
0x0000000000000000 8
0x0000000000000400 16
0x0000000000000800 32
0x0000000000000c00 64

F2F, F2I, I2F, I2I: srcWidth
0x0000000000000000 8
0x0000000000001000 16
0x0000000000002000 32
0x0000000000003000 64

F2F, F2I, I2F, I2I: destSign
0x0000000000000000 F
0x0000000000000000 U
0x0000000000008000 S

F2F, F2I, I2F, I2I: srcSign
0x0000000000000000 F
0x0000000000000000 U
0x0000000000008000 S

F2I, I2F, I2I: r20part
0x0000000000000000 H0
0x0000040000000000 H1
0x0000000000000000 B0
0x0000020000000000 B1
0x0000040000000000 B2
0x0000060000000000 B3

F2F: r20part
0x0000000000000000 H0
0x0000020000000000 H1

F2F: round
0x0000040000000000 ROUND
0x0000048000000000 FLOOR
0x0000050000000000 CEIL
0x0000058000000000 TRUNC

F2I: round
0x0000000000000000 ROUND
0x0000040000000000 FLOOR
0x0000080000000000 CEIL
0x00000c0000000000 TRUNC

HADD2, HMUL2: r8part
0x0001000000000000 H0_H0
0x0000000000000000 H1_H1

HFMA2: r20part
0x0000000020000000 H0_H0
0x0000000030000000 H1_H1

FADD, DADD, FMUL, DMUL, F2F, I2F: rnd
0x0000000000000000 RN
0x0000040000000000 RM
0x0000080000000000 RP
0x00000c0000000000 RZ

FMUL: mulf
0x0000100000000000 D2
0x0000200000000000 D4
0x0000300000000000 D8
0x0000400000000000 M8
0x0000500000000000 M4
0x0000600000000000 M2

BRA, JMP, RET, EXIT: CON
0x0000000000000000 F
0x0000000000000004 LT
0x0000000000000008 EQ
0x000000000000000c LE
0x0000000000000010 GT
0x0000000000000014 NE
0x0000000000000018 GE
0x000000000000001c NUM
0x0000000000000020 NAN
0x0000000000000024 LTU
0x0000000000000028 EQU
0x000000000000002c LEU
0x0000000000000030 GTU
0x0000000000000034 NEU
0x0000000000000038 GEU
0x0000000000000040 OFF
0x0000000000000044 LO
0x0000000000000048 SFF
0x000000000000004c LS
0x0000000000000050 HI
0x0000000000000054 SFT
0x0000000000000058 HS
0x000000000000005c OFT

MOV: lane2a
0x0000380000000000 LNONE
0x0000340000000000 L0
0x0000300000000000 L1
0x00002c0000000000 L01
0x0000280000000000 L2
0x0000240000000000 L02
0x0000200000000000 L12
0x00001c0000000000 L3
0x0000180000000000 L03
0x0000140000000000 L13
0x0000100000000000 L013
0x00000c0000000000 L23
0x0000080000000000 L023
0x0000040000000000 L123

MOV32I: lane0e
0x0000000000038000 LNONE
0x0000000000034000 L0
0x0000000000030000 L1
0x000000000002c000 L01
0x0000000000028000 L2
0x0000000000024000 L02
0x0000000000020000 L12
0x000000000001c000 L3
0x0000000000018000 L03
0x0000000000014000 L13
0x0000000000010000 L013
0x000000000000c000 L23
0x0000000000008000 L023
0x0000000000004000 L123

DFMA: rnd
0x0000000000000000 RN
0x0004000000000000 RM
0x0008000000000000 RP
0x000c000000000000 RZ

FFMA: rnd
0x0000000000000000 RN
0x0040000000000000 RM
0x0080000000000000 RP
0x00c0000000000000 RZ

FFMA, FMUL32I
0x0100000000000000 FTZ

F2F, F2I, FADD, FMUL, FMNMX
0x0000800000000000 FTZ

FADD32I
0x0080000000000000 FTZ

FMUL32I
0x0020000000000000 FTZ

FSET, FSETP, FCMP, DSET, DSETP
0x0400000000000000 FTZ

HADD2, HMUL2
0x0000008000000000 FTZ

HFMA2
0x0000002000000000 FTZ

FADD, FFMA, FMUL, F2F, I2I, MUFU, IMAD, IADD, ISUB
0x0020000000000000 SAT

FADD, DADD, FMNMX, DMNMX, MUFU, FFMA, DFMA, FMUL, DADD, DMUL
0x0008000000000000 r8neg

FADD, DADD, FMNMX, DMNMX, RRO, F2F, F2I, I2F, I2I
0x0001000000000000 r20neg

FMUL, DMUL, FFMA, DFMA
0x0001000000000000 r20neg

FFMA, DFMA
0x0010000000000000 r39neg

FADD, DADD, FMNMX, DMNMX, MUFU
0x0002000000000000 r8abs

FADD, DADD, FMNMX, DMNMX, F2F, F2I, I2F, I2I
0x0010000000000000 r20abs

FSETP, DSETP, FSET, DSET
0x0000400000000000 r8neg
0x0100000000000000 r20neg
0x0200000000000000 r8abs
0x0000800000000000 r20abs

RRO: func
0x0000000000000000 SINCOS
0x0000040000000000 EX2

MUFU: func
0x0000000000000000 COS
0x0000000000800000 SIN
0x0000000001000000 EX2
0x0000000001800000 LG2
0x0000000002000000 RCP
0x0000000002800000 RSQ
0x0000000003000000 RCP64H
0x0000000003800000 RSQ64H

FSETP, DSETP, FSET, DSET, FCMP: cmp
0x0008000000000000 .LT
0x0010000000000000 .EQ
0x0018000000000000 .LE
0x0020000000000000 .GT
0x0020000000000000
0x0028000000000000 .NE
0x0030000000000000 .GE
0x0038000000000000 .NUM
0x0040000000000000 .NAN
0x0048000000000000 .LTU
0x0050000000000000 .EQU
0x0058000000000000 .LEU
0x0060000000000000 .GTU
0x0068000000000000 .NEU
0x0070000000000000 .GEU

FSETP, DSETP, FSET, DSET: bool
0x0000000000000000 AND
0x0001000000000000 OR
0x0002000000000000 XOR

HSETP2: cmp
0x0000002800000000 .NE

HSETP2: bool
0x0000000000000000 AND

S2R: sr
0x0000000000000000  LANEID
0x0000000001000000  VIRTCFG
0x0000000001800000  VIRTID
0x0000000002000000  PM0
0x0000000002800000  PM1
0x0000000003000000  PM2
0x0000000003800000  PM3
0x0000000004000000  PM4
0x0000000004800000  PM5
0x0000000005000000  PM6
0x0000000005800000  PM7
0x0000000008000000  PRIM_TYPE
0x0000000008800000  INVOCATION_ID
0x0000000009000000  Y_DIRECTION
0x0000000010000000  TID
0x0000000010800000  TID.X
0x0000000011000000  TID.Y
0x0000000011800000  TID.Z
0x0000000012000000  CTA_PARAM
0x0000000012800000  CTAID.X
0x0000000013000000  CTAID.Y
0x0000000013800000  CTAID.Z
0x0000000014000000  NTID
0x0000000014800000  CirQueueIncrMinusOne
0x0000000015000000  NLATC
0x0000000015800000  43
0x0000000016000000  44
0x0000000016800000  45
0x0000000017000000  46
0x0000000017800000  47
0x0000000018000000  SWINLO
0x0000000018800000  SWINSZ
0x0000000019000000  SMEMSZ
0x0000000019800000  SMEMBANKS
0x000000001a000000  LWINLO
0x000000001a800000  LWINSZ
0x000000001b000000  LMEMLOSZ
0x000000001b800000  LMEMHIOFF
0x000000001c000000  EQMASK
0x000000001c800000  LTMASK
0x000000001d000000  LEMASK
0x000000001d800000  GTMASK
0x000000001e000000  GEMASK
0x0000000020000000  GLOBALERRORSTATUS
0x0000000021000000  WARPERRORSTATUS
0x0000000028000000  CLOCKLO
0x0000000029000000  GLOBALTIMERLO
0x0000000029800000  GLOBALTIMERHI

CS2R: sr
0x0000000005000000 CLOCKLO
0x0000000005100000 CLOCKHI
0x0000000005200000 GLOBALTIMERLO
0x0000000005300000 GLOBALTIMERHI

B2R
0x0000e00000000000 nop45

BAR: red
0x0000000000000000 POPC
0x0000000800000000 AND
0x0000001000000000 OR

MEMBAR: mode
0x0000000000000000 CTA
0x0000000000000100 GL
0x0000000000000200 SYS

VOTE: mode
0x0000000000000000 ALL
0x0008000000000000 ANY
0x0010000000000000 EQ

VOTE
0x00000000000003fc nor0

BRA
0x0000000000000200 U

TLDS: chnls
0x0010000000000000 RGBA

TLDS
0x0002000000000000 NODEP

LD, ST, LDG, STG, LDS, STS, LDL, STL, LDC, RED, ATOM, ATOMS
0x0000000000000000 nor8

LD, ST: type
0x0000000000000000 .U8
0x0100000000000000 .S8
0x0200000000000000 .U16
0x0300000000000000 .S16
0x0400000000000000
0x0400000000000000 .32
0x0500000000000000 .64
0x0600000000000000 .128

LDX: type
0x0000000000000000 .b32
0x0004000000000000 .b64
0x0008000000000000 .b96
0x000c000000000000 .b128

LD, ST: cache
0x0000000000000000 CG
0x1000000000000000 CS
0x1800000000000000 CV
0x1800000000000000 WT

STG, LDS, STS, LDL, STL, LDC: type
0x0000000000000000 .U8
0x0008000000000000 .S8
0x0010000000000000 .U16
0x0018000000000000 .S16
0x0020000000000000
0x0020000000000000 .32
0x0028000000000000 .64
0x0030000000000000 .128

LDG: type
0x0000000000000000 .U8
0x0000800000000000 .S8
0x0001000000000000 .U16
0x0001800000000000 .S16
0x0002000000000000
0x0002000000000000 .32
0x0002800800000000 .64
0x0003003800000000 .128

LDG, STG: cache
0x0000000000000000 CG
0x0000000000000000 CI
0x0000040000000000 CS
0x0000000000000000 CV
0x0000000000000000 WT

LDG
0x0000008000000000 E

LDL: cache
0x0000200000000000 CI

LDL, STL: cache
0x0000800000000000 CG
0x0001000000000000 LU
0x0001800000000000 CV
0x0001800000000000 WT

LDC: cache
0x0000100000000000 IL

STG, LDS, STS, LDL, STL, LDC
0x0000200000000000 E

LDS
0x0008000000000000 U

RED: type
0x0000000000000000
0x0010000000000000 .S32
0x0020000000000000 .U64
0x0030000000000000 .F32.FTZ.RN
0x0040000000000000 .F16x2.FTZ.RN
0x0050000000000000 .S64

RED: mode
0x0000000000000000 ADD
0x0080000000000000 MIN
0x0100000000000000 MAX
0x0180000000000000 INC
0x0200000000000000 DEC
0x0280000000000000 AND
0x0300000000000000 OR
0x0380000000000000 XOR

ATOM: type
0x0000000000000000
0x0002000000000000 .S32
0x0004000000000000 .U64
0x0006000000000000 .F32.FTZ.RN
0x0008000000000000 .F16x2.FTZ.RN
0x000a000000000000 .S64
0x0002000000000000 .64

ATOM, RED
0x0008000000000000 E

LD, ST
0x0080000000000000 E

ATOM: mode
0x0000000000000000 ADD
0x0010000000000000 MIN
0x0020000000000000 MAX
0x0030000000000000 INC
0x0040000000000000 DEC
0x0050000000000000 AND
0x0060000000000000 OR
0x0070000000000000 XOR
0x0080000000000000 EXCH
0x03f0000000000000 CAS

ATOMS: type
0x0000000000000000
0x0000000010000000 .S32
0x0000000020000000 .U64
0x0000000030000000 .S64
0x0010000000000000 .64

ATOMS: mode
0x0000000000000000 ADD
0x0010000000000000 MIN
0x0020000000000000 MAX
0x0030000000000000 INC
0x0040000000000000 DEC
0x0050000000000000 AND
0x0060000000000000 OR
0x0070000000000000 XOR
0x0080000000000000 EXCH
0x0240000000000000 CAS

BFE:REV2B
0x0000080000000000 REV2B
};

# The existence of a capture group can map directly to an op code adjustment, or...
# The named capture group value can map the op code adjustmemt from among several options
our %flags;
my (@ops, $flag);
foreach my $line (@flags)
{
    if ($line =~ m'^(0x[0-9a-z]+)\s*(.*)')
    {
        my $val = hex($1);
        # named rules (op: name)
        if ($flag)
            { $flags{$_}{$flag}{$2} = $val foreach @ops; }
        # simple existence check rules
        else
            { $flags{$_}{$2}        = $val foreach @ops; }
    }
    else
    {
        my ($ops, $name) = split ':\s*', $line;
        @ops = split ',\s*', $ops;
        $flag = $name;
    }
}

sub parseInstruct
{
    my ($inst, $grammar) = @_;
    return unless $inst =~ $grammar->{rule};
    my %capData = %+;
    #print Dumper(\%capData);
    return \%capData;
}

# for immediate or constant operands and a given opcode, bits 56-63 get transformed
my %immedOps = map { $_ => 1 } qw(i20 f20 d20);
#Donot use immedCodes, use a seperate grammar rule
my %immedCodes =
(
    0x5c => 0x64,
    0x5b => 0x6d,
    0x59 => 0x6b,
    0x58 => 0x68,
);
my %constCodes =
(
    #DST, SRC1, C
    #DST, SRC1, SRC3, C
    c20 => 0x2,
    #DST, SRC1, C, SRC3
    c39 => 0x1,
);
my %reuseCodes = (reuse1 => 1, reuse2 => 2, reuse3 => 4);

# just pick out the reuse code and nothing else
sub genReuseCode
{
    my $capData = shift;
    my $reuse = 0;
    $reuse |= $reuseCodes{$_} foreach grep $capData->{$_}, keys %reuseCodes;
    return $reuse;
}

# Generate an op code from regex capture data
# if you pass in a test array ref it will populate it with the matching capture groups
sub genCode
{
    my ($op, $grammar, $capData, $test) = @_;

    my $flags     = $flags{$op};
    my $code      = $grammar->{code};
    my $reuse     = 0;
    #my $immedCode = $immedCodes{$code >> 56};

    #print map "$_: $capData->{$_}\n", keys %capData if $op eq 'I2I';

    # process the instruction predicate (if valid for this instuction)
    if (exists $capData->{noPred})
    {
        delete $capData->{noPred};
        push @$test, 'noPred' if $test;
    }
    else
    {
        my $p = defined($capData->{predNum}) ? $capData->{predNum} : 7;
        push @$test, 'predNum' if $test;
        if (exists $capData->{predNot})
        {
            $p |= 8;
            push @$test, 'predNot' if $test;
        }
        #$code ^= $p << 16;
        #predicate 21~18 bit
        $code |= $p << 18;
        delete @{$capData}{qw(predNum predNot)};

    }
    # process the register reuse flags
    foreach my $rcode (qw(reuse1 reuse2 reuse3))
    {
        if (delete $capData->{$rcode})
        {
            $reuse |= $reuseCodes{$rcode};
            push @$test, $rcode if $test;
        }
    }

    foreach my $capture (keys %$capData)
    {
        # change the base code for immediate versions of the op
        #if (exists $immedOps{$capture})
        #    { $code ^= $immedCode << 56; }
        # change the base code for constant versions of the op
        #elsif (exists $constCodes{$capture})
        if (exists $constCodes{$capture})
            { $code ^= $constCodes{$capture} << 62; }
            #{ $code ^= $constCodes{$capture} << 56; }

        # if capture group is an operand then process and add that data to code
        if (exists $operands{$capture})
        {
            # don't process the r20 that comes with the r39s20 capture
            unless ($capture eq 'r20' && exists $capData->{r39s20})
            {
                $code ^= $operands{$capture}->($capData->{$capture});
                push @$test, $capture if $test;
            }
        }

        # Add matching flags (an operand might also add/remove a flag)
        if (exists $flags->{$capture})
        {
            # a named multivalue flag
            if (ref $flags->{$capture})
            {
                #$code |= $flags->{$capture}{$capData->{$capture}};
                $code ^= $flags->{$capture}{$capData->{$capture}};
                push @$test, "$capture:$capData->{$capture}" if $test;
            }
            # a simple exists flag
            else
            {
                #$code |= $flags->{$capture};
                $code ^= $flags->{$capture};
                push @$test, $capture if $test;
            }
        }
        elsif (!exists $operands{$capture} && !$test)
        {
            # Every capture group should be acted upon.  Missing one is a bug.
            warn "UNUSED: $op: $capture: $capData->{$capture}\n";
            warn Dumper($flags);
        }
    }

    return $code, $reuse;
}


#my $CtrlRe = qr'(?<ctrl>[0-9a-fA-F\-]{2}:[1-6\-]:[1-6\-]:[\-yY]:[0-9a-fA-F])';
#my $CtrlRe = qr'(?<ctrl>0x[0-9a-fA-F]{2})';
my $CtrlRe = qr'(?<ctrl>[T\-]:[G\-]:[D\-]:[S\-]:[0-9]{2})';
my $PredRe = qr'(?<pred>@!?(?<predReg>P\d)\s+)';
my $InstRe = qr"$PredRe?(?<op>\w+)(?<rest>[^;]*;)"o;
my $CommRe = qr'(?<comment>.*)';

sub processAsmLine
{
    my ($line, $lineNum) = @_;

    if ($line =~ m"^$CtrlRe(?<space>\s+)$InstRe$CommRe"o)
    {
        return {
            lineNum => $lineNum,
            pred    => $+{pred},
            predReg => $+{predReg},
            space   => $+{space},
            op      => $+{op},
            comment => $+{comment},
            inst    => normalizeSpacing($+{pred} . $+{op} . $+{rest}),
            ctrl    => readCtrl($+{ctrl}, $line),
        };
    }
    return undef;
}

sub processSassLine
{
    my $line = shift;

    if ($line =~ m"^\s+/\*(?<num>[0-9a-f]+)\*/\s+$InstRe\s+/\* (?<code>0x[0-9a-f]+)"o)
    {
        return {
            num     => hex($+{num}),
            pred    => $+{pred},
            op      => $+{op},
            ins     => normalizeSpacing($+{op} . $+{rest}),
            inst    => normalizeSpacing($+{pred} . $+{op} . $+{rest}),
            code    => hex($+{code}),
        };
    }
    return undef;
}

sub processSassCtrlLine
{
    my ($line, $ctrl, $ruse) = @_;

    return 0 unless $line =~ m'^\s+\/\* (0x[0-9a-f]+)';

    my $code = hex($1);
    if (ref $ctrl)
    {
        #modify by wb: add 4 sentences to handle kepler ctrol code
        push @$ctrl, ($code & 0x00000000000003fc) >> 2;
        push @$ctrl, ($code & 0x000000000003fc00) >> 10;
        push @$ctrl, ($code & 0x0000000003fc0000) >> 18;
        push @$ctrl, ($code & 0x00000003fc000000) >> 26;
        push @$ctrl, ($code & 0x000003fc00000000) >> 34;
        push @$ctrl, ($code & 0x0003fc0000000000) >> 42;
        push @$ctrl, ($code & 0x03fc000000000000) >> 50;
    }
    if (ref $ruse)
    {
        push @$ruse, ($code & 0x00000000001e0000) >> 17;
        push @$ruse, ($code & 0x000003c000000000) >> 38;
        push @$ruse, ($code & 0x7800000000000000) >> 59;
        push @$ruse, ($code & 0x00000000001e0000) >> 17;
        push @$ruse, ($code & 0x000003c000000000) >> 38;
        push @$ruse, ($code & 0x7800000000000000) >> 59;
        push @$ruse, ($code & 0x7800000000000000) >> 59;
    }
    return 1;
}

sub replaceXMADs
{
    my $file = shift;

# XMAD.LO d, a, b, c, x;
# ----------------------
# XMAD.MRG x, a, b.H1, RZ;
# XMAD d, a, b, c;
# XMAD.PSL.CBCC d, a.H1, x.H1, d;
# ----------------------
# XMAD d, a, 0xffff, c;
# XMAD.PSL d, a.H1, 0xffff, d;
    $file =~ s/\n\s*$CtrlRe(?<space>\s+)($PredRe)?XMAD\.LO\s+(?<d>\w+)\s*,\s*(?<a>\w+)\s*,\s*(?<b>\w+)\s*,\s*(?<c>c\[$hex\]\[$hex\]|\w+)\s*,\s*(?<x>\w+)\s*;$CommRe/

        die "XMAD.LO: Destination and first operand cannot be the same register ($+{d})." if $+{d} eq $+{a};
        sprintf '
%1$s%2$s%3$sXMAD.MRG %8$s, %5$s, %6$s.H1, RZ;%9$s
%1$s%2$s%3$sXMAD %4$s, %5$s, %6$s, %7$s;
%1$s%2$s%3$sXMAD.PSL.CBCC %4$s, %5$s.H1, %8$s.H1, %4$s;',
                @+{qw(ctrl space pred d a b c x comment)}
    /egmos;

    $file =~ s/\n\s*$CtrlRe(?<space>\s+)($PredRe)?XMAD(?<mod>(?:\.[SU]16)(?:\.[SU]16))?\.LO2\s+(?<d>\w+)\s*,\s*(?<a>\w+)\s*,\s*(?<b>-?$immed|\w+)\s*,\s*(?<c>c\[$hex\]\[$hex\]|\w+)\s*;$CommRe/

        die "XMAD.LO2: Destination and first operand cannot be the same register ($+{d})." if $+{d} eq $+{a};
        sprintf '
%1$s%2$s%3$sXMAD%9$s %4$s, %5$s, %6$s, %7$s;%8$s
%1$s%2$s%3$sXMAD%9$s.PSL %4$s, %5$s.H1, %6$s, %4$s;',
            @+{qw(ctrl space pred d a b c comment mod)}
    /egmos;

    $file =~ s/\n\s*$CtrlRe(?<space>\s+)($PredRe)?XMAD(?<mod>(?:\.[SU]16)(?:\.[SU]16))?\.LO2C\s+(?<d>\w+)\s*,\s*(?<a>\w+)\s*,\s*(?<b>c\[$hex\]\[$hex\]|\w+)\s*,\s*(?<c>\w+)\s*;$CommRe/

        die "XMAD.LO2C: Destination and first operand cannot be the same register ($+{d})." if $+{d} eq $+{a};
        sprintf '
%1$s%2$s%3$sXMAD%9$s %4$s, %5$s, %6$s, %7$s;%8$s
%1$s%2$s%3$sXMAD%9$s.PSL %4$s, %5$s, %6$s.H1, %4$s;',
            @+{qw(ctrl space pred d a b c comment mod)}
    /egmos;

    #TODO: add more XMAD macros
    return $file;
}
# convert extra spaces to single spacing to make our re's simplier
sub normalizeSpacing
{
    my $inst = shift;
    $inst =~ s/\t/ /g;
    $inst =~ s/\s{2,}/ /g;
    return $inst;
}


# map binary control notation on to easier to work with format.
sub printCtrl
{
    my $code = shift;

    my $stall = ($code & 0x0f) >> 0;
    my $sharedbar = ($code & 0x10) >> 4;
    my $dual_issue = ($code & 0x20) >> 5;
    my $globalbar = ($code & 0x40) >> 6;
    my $texbar = ($code & 0x80) >> 7;
    #my $stall = ($code & 0x0000f) >> 0;
    #my $yield = ($code & 0x00010) >> 4;
    #my $wrtdb = ($code & 0x000e0) >> 5;  # write dependency barier
    #my $readb = ($code & 0x00700) >> 8;  # read  dependency barier
    #my $watdb = ($code & 0x1f800) >> 11; # wait on dependency barier

    #$yield = $yield ? '-' : 'Y';
    #$wrtdb = $wrtdb == 7 ? '-' : $wrtdb + 1;
    #$readb = $readb == 7 ? '-' : $readb + 1;
    #$watdb = $watdb ? sprintf('%02x', $watdb) : '--';
    $texbar = $texbar ? 'T' : '-';
    $globalbar = $globalbar ? 'G' : '-';
    $dual_issue = $dual_issue ? '-' : 'D';
    $sharedbar = $sharedbar ? 'S' : '-';
    $stall = sprintf('%02d', $stall);
    #right justify,binary value, padding 0s
    #return sprintf '%08b', $code;
    return sprintf '%s:%s:%s:%s:%02d', $texbar, $globalbar, $dual_issue, $sharedbar, $stall;
    #return sprintf '%s:%s:%s:%s:%x', $watdb, $readb, $wrtdb, $yield, $stall;
}
sub readCtrl
{
    my ($ctrl, $context) = @_;
    #print $ctrl;
    my ($texbar, $globalbar, $dual_issue, $sharedbar, $stall) = split ':', $ctrl;
    #my ($watdb, $readb, $wrtdb, $yield, $stall) = split ':', $ctrl;

    $texbar= $texbar eq 'T' ? 1 : 0;
    $globalbar= $globalbar eq 'G' ? 1 : 0;
    $dual_issue= $dual_issue eq 'D' ? 0 : 1;
    $sharedbar= $sharedbar eq 'S' ? 1 : 0;
    $stall = sprintf("%d", $stall);
    #$stall = sprintf("%04b", $stall);

    #$watdb = $watdb eq '--' ? 0 : hex $watdb;
    #$readb = $readb eq '-'  ? 7 : $readb - 1;
    #$wrtdb = $wrtdb eq '-'  ? 7 : $wrtdb - 1;
    #$yield = $yield eq 'y' || $yield eq 'Y'  ? 0 : 1;
    #$stall = hex $stall;

    #die sprintf('wait dep out of range(0x00-0x3f): %x at %s',   $watdb, $context) if $watdb != ($watdb & 0x3f);

    return
        $texbar << 7 |
        $globalbar << 6 |
        $dual_issue << 5 |
        $sharedbar << 4 |
        $stall;
#  $watdb << 11 |
#        $readb << 8  |
#        $wrtdb << 5  |
#        $yield << 4  |
#        $stall << 0;
}

sub getRegNum
{
    my ($regMap, $regName) = @_;

    return !exists($regMap->{$regName}) || ref($regMap->{$regName}) ? $regName : $regMap->{$regName};
}

sub getVecRegisters
{
    my ($vectors, $capData) = @_;
    my $regName = $capData->{r0} or return;

    return if $regName eq 'RZ';

    if ($capData->{type} eq '.64' || $capData->{i31w4} eq '0x3')
    {
        if ($regName =~ m'^R(\d+)$')
        {
            return map "R$_", ($1 .. $1+1);
        }
        confess "$regName not a 64bit vector register" unless exists $vectors->{$regName};
        return @{$vectors->{$regName}}[0,1];
    }
    if ($capData->{type} eq '.128' || $capData->{i31w4} eq '0xf')
    {
        if ($regName =~ m'^R(\d+)$')
        {
            return map "R$_", ($1 .. $1+3);
        }
        confess "$regName not a 128bit vector register" unless exists($vectors->{$regName}) && @{$vectors->{$regName}} == 4;
        return @{$vectors->{$regName}};
    }
    return $regName;
}

sub getAddrVecRegisters
{
    my ($vectors, $capData) = @_;
    my $regName = $capData->{r8} or return;

    return if $regName eq 'RZ';

    if (exists $capData->{E})
    {
        if ($regName =~ m'^R(\d+)$')
        {
            return map "R$_", ($1 .. $1+1);
        }
        print Dumper($vectors) unless exists $vectors->{$regName};
        confess "$regName not a 64bit vector register" unless exists $vectors->{$regName};
        return @{$vectors->{$regName}}[0,1];
    }
    return $regName;
}

__END__



