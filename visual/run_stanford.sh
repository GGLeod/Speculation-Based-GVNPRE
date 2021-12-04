#!/bin/bash

touch log.txt
echo " " > log.txt
for benchmark in Bubblesort FloatMM intMM Oscar Perm Puzzle Queens Quicksort RealMM Towers Treesort; do
echo "Running...${benchmark}" >> log.txt
./run.sh ${benchmark} >> log.txt
echo "Complete...${benchmark} with exit code $?" >> log.txt
done
