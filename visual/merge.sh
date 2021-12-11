TIME_MEASURE=../res/${1}_spgvn_${2}.txt

opt -o ${1}/${1}.merge.bc -load ../MERGE/build/src/LLVMHW2.so -mergeblock < ${1}/${1}_final.bc > /dev/null

opt -dot-cfg < ${1}/${1}.merge.bc > /dev/null

dot -Tpng .${1}.dot -o ${1}/${1}_merge.png

echo -e "\n\n\n4. Result for merge" >> ${TIME_MEASURE}
echo -e "\n\n   compile" >> ${TIME_MEASURE}
{ time clang ${1}/${1}.merge.bc -o ${1}/${1}_merge; } 2>> ${TIME_MEASURE}
echo -e "\n\n   run" >> ${TIME_MEASURE}
{ time ${1}/${1}_merge ; } 2>> ${TIME_MEASURE}