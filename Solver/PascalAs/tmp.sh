#!/bin/bash
prefix=./ptxgen/data_sm_60/
asm=$prefix"asm/*.sass"
for f in $asm
do
    cat $f >> all.sass
done
### ignore  non instruction lines ####
ptxgen/extract.awk all.sass > all_inst.sass
### make instruction uniq ###
python ptxgen/uniq.py all_inst.sass > sm_60.sass


