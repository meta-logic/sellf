#!/bin/bash

cd src
make 
make doc
cp sellf ../
cd ../doc
pdflatex sellfdoc.tex
pdflatex sellfdoc.tex
rm sellfdoc.tex
rm sellfdoc.aux
rm sellfdoc.log
rm sellfdoc.toc
rm ocamldoc.sty

