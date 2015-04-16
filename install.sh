#!/bin/bash

cd src
make 
make doc
#Fix relative paths before uncommenting this
#cp sellf ../
cd ../doc
pdflatex sellfdoc.tex
pdflatex sellfdoc.tex
rm sellfdoc.tex
rm sellfdoc.aux
rm sellfdoc.log
rm sellfdoc.toc
rm ocamldoc.sty

