#! /bin/bash

experiment_dir="./experiments"
groups=( \
  "api-refinement" \
  "blackjack" \
  "ctl" \
  "delimited-release" \
  "flaky-tests" \
  "gni" \
  "param-usage" \
)

output_dir="$experiment_dir/_results"

mkdir -p "$output_dir"

for group in "${groups[@]}"
do
  group_output_dir="$output_dir/$group"
  mkdir -p "$group_output_dir"
  for exfile in $experiment_dir/$group/*.imp
  do
    echo -n "$exfile... "
    bname=$(basename -- "$exfile")
    exname="${bname%.*}"
    start=$(($(date +%s%N)/1000000))
    if (time stack exec orhle-exe $exfile) > "$group_output_dir/$exname".out 2>&1;
    then
       echo -ne "\xE2\x9C\x94"
    else
       echo -ne "\xE2\x9D\x8C"
    fi
    end=$(($(date +%s%N)/1000000))
    echo "  ($((end-start)) ms)"
  done
done
