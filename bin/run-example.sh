#! /bin/bash

mkdir -p ./example-output/$1
stack build && (time stack exec orhle-exe ./examples/$1/$2.imp) 2>&1 | tee ./example-output/$1/$2.out
