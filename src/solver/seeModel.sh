#!/bin/bash

# Script for getting the model as it is parsed by sellf

dlvhex -s filename.in | sed "s/{//" | sed "s/}/./" | sed "s/[a-zA-Z]*\(\), /. /g" | sed "s/\./.\n/g" > model.txt
