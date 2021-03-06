#!/bin/bash
### run.sh
### benchmark runner script
### Locate this script at each benchmark directory. e.g, 583simple/run.sh
### usage: ./run.sh ${benchmark_name} ${input} 
### e.g., ./run.sh compress compress.in or ./run.sh simple

PATH_MYPASS=../build/SPGVNPRE/LLVMHW2.so ### Action Required: Specify the path to your pass ###
NAME_MYPASS=-spgvnpre ### Action Required: Specify the name for your pass ###
BENCH=../test/${1}.c
TIME_MEASURE=../res/${1}_spgvn.txt

# INPUT=${2}

# setup(){
# if [[ ! -z "${INPUT}" ]]; then
# echo "INPUT:${INPUT}"
# ln -sf input1/${INPUT} .
# fi
# }
mkdir -p ${1}

rm ${1}/*

# Prepare input to run
# setup
# Convert source code to bitcode (IR)
# This approach has an issue with -O2, so we are going to stick with default optimization level (-O0)
clang -Xclang -disable-O0-optnone -emit-llvm -c ${BENCH} -o ${1}/${1}.bc 

echo -e "\n\n\n1. Result for reg" > ${TIME_MEASURE}
echo -e "\n\n   compile" >> ${TIME_MEASURE}
{ time clang ${1}/${1}.bc -o ${1}/${1}; } 2>> ${TIME_MEASURE}
echo -e "\n\n   run" >> ${TIME_MEASURE}
{ time lli ${1}/${1}.bc; } 2>> ${TIME_MEASURE}


opt -mem2reg -dce ${1}/${1}.bc -o ${1}/${1}_reg.bc



opt -dot-cfg < ${1}/${1}_reg.bc > /dev/null

dot -Tpng .${1}.dot -o ${1}/${1}_reg.png


# opt -gvn -enable-pre ${1}/${1}_reg.bc -o ${1}/${1}_pre.bc
# opt -dot-cfg < ${1}/${1}_pre.bc > /dev/null
# dot -Tpng .${1}.dot -o ${1}/${1}_pre.png

# echo -e "\n\n\n2. Result for pre" >> ${TIME_MEASURE}
# { time lli ${1}/${1}_pre.bc; } 2>>  ${TIME_MEASURE}



# Instrument profiler
opt -pgo-instr-gen -instrprof ${1}/${1}_reg.bc -o ${1}/${1}.prof.bc 
# Generate binary executable with profiler embedded

clang -fprofile-instr-generate ${1}/${1}.prof.bc -o ${1}/${1}.prof;

# Collect profiling data
${1}/${1}.prof > ${1}/correct_output

# Translate raw profiling data into LLVM data format
llvm-profdata merge -output=pgo.profdata default.profraw


# Prepare input to run
# setup
# Apply your pass to bitcode (IR)
opt -o ${1}/${1}.spre.bc -pgo-instr-use -pgo-test-profile-file=pgo.profdata -load ${PATH_MYPASS} ${NAME_MYPASS} < ${1}/${1}_reg.bc > /dev/null

opt -dot-cfg < ${1}/${1}.spre.bc > /dev/null

dot -Tpng .${1}.dot -o ${1}/${1}_spre.png

echo -e "\n\n\n2. Result for spre" >> ${TIME_MEASURE}
echo -e "\n\n   run" >> ${TIME_MEASURE}
{ time lli ${1}/${1}.spre.bc ; } 2>> ${TIME_MEASURE}

# perform dead code elimination

opt -dce ${1}/${1}.spre.bc -o ${1}/${1}_final.bc

opt -dot-cfg < ${1}/${1}_final.bc > /dev/null

dot -Tpng .${1}.dot -o ${1}/${1}_final.png
echo -e "\n\n\n3. Result for final" >> ${TIME_MEASURE}
echo -e "\n\n   compile" >> ${TIME_MEASURE}
{ time clang ${1}/${1}_final.bc -o ${1}/${1}_final; } 2>> ${TIME_MEASURE}
echo -e "\n\n   run" >> ${TIME_MEASURE}
{ time lli ${1}/${1}_final.bc ; } 2>> ${TIME_MEASURE}

opt -o ${1}/${1}.merge.bc -load ../MERGE/build/src/LLVMHW2.so -mergeblock < ${1}/${1}_final.bc > /dev/null

opt -dot-cfg < ${1}/${1}.merge.bc > /dev/null

dot -Tpng .${1}.dot -o ${1}/${1}_merge.png

echo -e "\n\n\n4. Result for merge" >> ${TIME_MEASURE}
echo -e "\n\n   compile" >> ${TIME_MEASURE}
{ time clang ${1}/${1}.merge.bc -o ${1}/${1}_merge; } 2>> ${TIME_MEASURE}
echo -e "\n\n   run" >> ${TIME_MEASURE}
{ time lli ${1}/${1}.merge.bc ; } 2>> ${TIME_MEASURE}

rm .*