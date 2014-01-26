#!/bin/bash

cd src
make 
make doc
cp sellf ../
cd ../doc
pdflatex sellfdoc.tex

