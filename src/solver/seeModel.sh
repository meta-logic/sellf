#!/bin/bash

dlvhex -s temp_perm0.in | sed "s/{//" | sed "s/}/./" | sed "s/[a-zA-Z]*\(\), /. /g" | sed "s/\./.\n/g" > model.txt
