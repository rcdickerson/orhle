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
  "delimited-release/avg-salaries-no-dr" \
  "delimited-release/avg-salaries" \
  "delimited-release/conditional-leak" \
  "delimited-release/conditional-no-dr" \
  "delimited-release/conditional" \
  "delimited-release/median-no-dr" \
  "delimited-release/median" \
  "delimited-release/parity-fun" \
  "delimited-release/parity-no-dr" \
  "delimited-release/parity" \
  "delimited-release/parity2" \
  "delimited-release/wallet-no-dr" \
  "delimited-release/wallet" \
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
mkdir -p ./example-output/api-refinement
mkdir -p ./example-output/delimited-release
mkdir -p ./example-output/gni
mkdir -p ./example-output/param-usage

for ex in "${examples[@]}"
do
  echo -n "$ex... "
  start=$(($(date +%s%N)/1000000))
  if (time stack exec klive-exe ./examples/$ex.imp) > ./example-output/$ex.out 2>&1;
  then
     echo -ne "\xE2\x9C\x94"
  else
     echo -ne "\xE2\x9D\x8C"
  fi
  end=$(($(date +%s%N)/1000000))
  echo "  ($((end-start)) ms)"
done
