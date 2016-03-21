#!/bin/bash

cd src
make 
# It is important that make is run before make doc to generate the cmi files.
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

