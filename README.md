# Speculation-Based-GVNPRE


Partial redundancy elimination (PRE) is a method that removes partial redundancies on some paths by hoisting the computation up on other paths. The transformation makes the computation fully redundant and therefore can be eliminated. Speculation-based PRE (SPRE) further uses profiling information to do more aggressive partial redundancy elimination. In this project, we implemented value-based speculative PRE (SGVNPRE) based on edge-profiling information. Compared with the main reference paper, which is solely based on lexical equivalence, we care about value equivalence and incorporated value-based PRE in our algorithm. We also make our algorithm work based on the SSA form, which are not implemented in the original paper. We further compare our result with the global value based PRE (GVNPRE) to see if there is any speedup in terms of runtime. To the best of our knowledge, this comparison is not done in any published paper. We evaluate our algorithm on simple self-designed testcases as well as a subset of LLVM SingleSource Benchmarks. Results showed that for the limited testcases we tried, SGVNPRE is slower than GVNPRE and we provided potential explanations and solutions for this.

The main source code is at SPGVNPRE/PASS.cpp. Try "visual/single_copy.sh classic" too see the output of a classic example of SGVNPRE in visual/classic.
