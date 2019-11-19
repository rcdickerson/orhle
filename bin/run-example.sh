#! /bin/bash

mkdir -p ./examples/orhle-output
stack build && (time stack exec klive-exe ./examples/$1/$2.imp) > ./examples/orhle-output/$1/$2.out 2>&1
