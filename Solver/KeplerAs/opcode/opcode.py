from sets import Set
from subprocess import Popen, PIPE, STDOUT
import subprocess 
import struct
import sys
import os
def check_mode(arch):
    if (arch == "SM21" or arch=="Fermi" or arch == "SM35" or arch=="Kepler"):
        return 1
    elif (arch == "SM52" or arch == "Maxwell"):
        return 2
    elif (arch == "SM60" or arch == "Pascal"):
        return 3
    else:
        return 0

def dump(newcode, mode, arch):
    ##Raw binary
    if mode == 1:
        #print newcode
        #ff = '0x%016x' % newcode 
        base=int(newcode, 16)
        ff="tmp.bin"
        fout = open(ff, 'wb')
        fout.write(struct.pack('<Q', int(base)))
        fout.close()
        #nvdisasm -b  SM35 ff
        #redirect stderr to stdout
        cmd = 'nvdisasm -b SM35 %s 2>&1' % ff
        tmp = os.popen(cmd).read()
        rmfile = 'rm %s' % ff
        os.system(rmfile)
        return tmp
    elif mode == 2:
        if arch == "Maxwell" or arch == "SM52":
            f = open("test_sm52.cubin",'rb+')  
            f.seek(904) 
            base=int(newcode, 16)
            f.write(struct.pack('Q', int(base)))
            f.close()
            cmd = 'cuobjdump --gpu-architecture sm_52 --dump-sass test_sm52.cubin 2>&1'
            tmp = os.popen(cmd).read()
            return tmp
    elif mode == 3:
        if arch == "Pascal" or arch == "SM60":
            f = open("test_sm60.cubin",'rb+')  
            f.seek(904) 
            base=int(newcode, 16)
            f.write(struct.pack('Q', int(base)))
            f.close()
            cmd = 'cuobjdump --gpu-architecture sm_60 --dump-sass test_sm60.cubin 2>&1'
            tmp = os.popen(cmd).read()
            return tmp
        else: 
            print "You need to provide a cubin template and position of first instruction !"
            exit()
    else:
        print "Error dump mode !"
        exit()

class Inst:
    ### parse instruction to structure###
    ### inst is a list like this ["MOV", "R1,", "c[0x0][0x44];", "/*","0x64c03c00089c0006","*/"]
    def __init__(self, inst):
        l=len(inst)
        self.op = ""
        index = 0

        if inst[0] == '{':
            inst.pop(0)
        #check predicate, such as @P0
        if (inst[index].find("@") != -1):
            self.pred=inst[index]
            inst.pop(0) #pop out predicate
        #check opcode
        if inst[index][len(inst[index]) - 1] == ";" :
            str=inst[index][0:len(inst[index]) -1 ]
        else:
            str = inst[index]
        op = str.split(".");
        self.op = op[0]

    def printInst(self):
        print self.op


if __name__ == "__main__":
    count = 0;
    print "......................................................................."
    print " argv[1]: disasssembly file;"
    print " argv[2]: arch: SM21|SM35|Maxwell|Kepler|SM52 "
    pos=Set([])
    #with open("sm35.sass") as f:
    with open(sys.argv[1]) as f:
        for line in f:
            count += 1
            if count == 100:
                break
            #ATOM.E.ADD.F32.FTZ.RN R0, [R2], R0; /* 0x68380000001c0802 */
            list=line.split()
            ## the origininal instruction structure
            origin=Inst(list)
            ##find the 64-bit encodings
            enc = list[len(list)-2]
            base=int(enc, 16)
            ### bit by bit xor, to observe whether opcode chages, and guess what this bit represent
            for i in range(0, 64):
                ##################### compute opcode, shift 64-4 bits ###########
                mask = 2**i
                newcode = base ^ mask
                fname = hex(newcode)
                #################### disassemble the new code ##################
                mode = check_mode(sys.argv[2])
                ff = '0x%016x' % newcode 
                tmp = dump(ff, mode, sys.argv[2])

                """
                ff = '0x%016x' % newcode 
                fout = open(ff, 'wb')
                fout.write(struct.pack('<Q', int(newcode)))
                fout.close()
                cmd = 'nvdisasm -b SM35 %s 2>&1' % ff
                tmp = os.popen(cmd).read()
                rmfile = 'rm %s' % ff
                os.system(rmfile)
                """

                ### compare the disassemble to check which field changes: opcode, operand or modifer ###
                if tmp and tmp.find("?") == -1 and tmp.find("error") == -1:
                    instline=tmp.split("\n")
                    if (mode == 1):
                        inst = instline[1].split();
                    else:
                        inst = instline[5].split();
                    inst.pop(0)
                    #### parse the new generated disassembly ##
                    my=Inst(inst)
		    print inst
                    ### if opcode is changed, then this bit represent opcode, we find it!!! ###
                    ## LDG and TEX are the same instructions in fact 
                    ## RED and ATOM are the same instruction
                    if my.op != origin.op and len(inst) > 3 and not (my.op == "LDG" and origin.op == "TEX") and not (my.op == "TEX" and origin.op=="LDG") and not (my.op == "RED" and origin.op == "ATOM") and not (my.op == "ATOM" and origin.op == "RED"):
                        print "opcode changes: ", origin.op,"=>", my.op, "when bit [", i, "]is flipped"
                        pos.add(i)
    print ""
    print "Done: found out bits represents opcode on Kepler...."
    print "Opcodes positons:", pos
    print "Then we could enumate in the space...."
