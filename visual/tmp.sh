PATH_MYPASS=../build/SPGVNPRE/LLVMHW2.so ### Action Required: Specify the path to your pass ###
NAME_MYPASS=-spgvnpre ### Action Required: Specify the name for your pass ###
BENCH=../test/${1}.c
TIME_MEASURE=../res/${1}_spgvn.txt

opt -o ${1}/${1}.spre.bc -pgo-instr-use -pgo-test-profile-file=pgo.profdata -load ${PATH_MYPASS} ${NAME_MYPASS} < ${1}/${1}_pre.bc > /dev/null
