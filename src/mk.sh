#!/bin/bash
make clean
make
OCAMLRUNPARAM="b" ./sellf << EOF
#load ../examples/proofsystems/s4
#permute
0
1
and_over_and
#done
#exit
EOF