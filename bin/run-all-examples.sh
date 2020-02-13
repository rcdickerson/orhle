#! /bin/bash

examples=( \
  "api-refinement/add3-shuffled" \
  "api-refinement/add3-sorted" \
  "api-refinement/simple-refinement" \
  "api-refinement/simple-nonrefinement" \
  "api-refinement/conditional-refinement" \
  "api-refinement/conditional-nonrefinement" \
  "api-refinement/loop-refinement" \
  "api-refinement/loop-nonrefinement" \
  "gni/nondet-leak" \
  "gni/nondet-nonleak" \
  "gni/simple-leak" \
  "gni/simple-nonleak" \
  "gni/smith1" \
  "gni/denning1" \
  "gni/denning2" \
  "param-usage/completely-unused" \
  "param-usage/semantically-unused" \
  "param-usage/three-used" \
  "param-usage/nondet-used" \
  "param-usage/nondet-unused" \
)

stack build
mkdir -p ./examples/orhle-output

for ex in "${examples[@]}"
do
  echo "Running $ex..."
  (time stack exec klive-exe ./examples/$ex.imp) > ./examples/orhle-output/$ex.out 2>&1
done
