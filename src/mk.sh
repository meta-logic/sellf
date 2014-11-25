#!/bin/bash
make clean
make
OCAMLRUNPARAM="b" ./sellf -bipole << EOF
#load ../examples/proofsystems/ll
#permute
3
3
tensor_over_tensor_bipole
#done
#exit
EOF
OCAMLRUNPARAM="b" ./sellf << EOF
#load ../examples/proofsystems/ll
#permute
3
3
tensor_over_tensor
#done
#exit
EOF