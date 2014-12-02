#!/bin/bash
make clean
make
OCAMLRUNPARAM="b" ./sellf -bipole << EOF
#load ../examples/proofsystems/mlj
#permute
0
0
imp_over_imp_bipole
#done
#exit
EOF
OCAMLRUNPARAM="b" ./sellf << EOF
#load ../examples/proofsystems/mlj
#permute
0
0
imp_over_imp
#done
#exit
EOF