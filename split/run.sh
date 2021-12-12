#!/bin/bash
### run.sh
### benchmark runner script
### Locate this script at each benchmark directory. e.g, 583simple/run.sh
### usage: ./run.sh ${benchmark_name} ${input} 
### e.g., ./run.sh compress compress.in or ./run.sh simple

PATH_MYPASS=./build/src/LLVMHW2.so ### Action Required: Specify the path to your pass ###
NAME_MYPASS=-splitblock ### Action Required: Specify the name for your pass ###
BENCH=../visual/${1}/${1}_final.bc

opt -o ${1}.merge.bc -load ${PATH_MYPASS} ${NAME_MYPASS} < ${BENCH} > /dev/null

opt -dot-cfg < ${1}.merge.bc > /dev/null

dot -Tpng .${1}.dot -o ${1}_merge.png

# # perform dead code elimination

# opt -dce ${1}.pre.bc -o ${1}_final.bc

# opt -dot-cfg < ${1}_final.bc > /dev/null

# dot -Tpng .main.dot -o ${1}_final.png
