##Solver is to crack GPU ISA encodings

Output:

* bit position of opcode
* bit positions of operands for different operand type
* bit positions of modifier for each instruction

How to run the workflow?

The workflow is composed of four stage:

* generate PTX code
    * Generate PTX code (.ptx) in ptxgen directory
    * compile PTX to cubin
    * disassembly cubin to sass
    * These sass files are input of the following three solvers
    * Each line of sass files looks like this:
    * ./call_genDisassembly.sh
    
    /∗0048∗/ IADD R0, R2, R0; /∗0x4800000000201c03∗/
* opcode solver
    * opcode solver probe 64-bit binary code of sass file by flipping each bit
    and observe whether opcode changes.
    * One of the outputs is bits presents opcode, on Kepler GPU, it should be [63,62,61,60,59,58,57,56,55,54, 1,0]
    * ./opcode.sh
    * The output file is in currenct directory: opcode_sm35.sass or opcode_sm52.sass
    * check the result with the one I generated: opcode/opcode_sm35.sass or opcode/opcode_sm52.sass
    
* modifer solver
    * similar to opcode solver
    * The output should be 
    * ./modifier.sh
    * The output file is  in current directory:modifier_sm35.txt or modifier_sm52.txt
    * the result is all modifier combinations of the input instructions
* Operand solver
    * R: Register I: Immediate C: constant[][] M: Memory P:Predicate
    * ./operand.sh
    * the output file is in current dir: operand_sm35.txt or operand_sm52.txt
    * check the result with the one generated by me: operand/operand_sm35.txt or operand/operand_sm52.txt