#! /bin/bash

mkdir -p ./examples/orhle-output
stack build && (time stack exec klive-exe ./examples/$1/$2.imp) 2>&1 | tee ./examples/orhle-output/$1/$2.out
