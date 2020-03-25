#!/bin/bash

examples=( \
    "api_refinement/simple/refinement                       VALID" \
    "api_refinement/simple/nonrefinement                  INVALID" \
    "api_refinement/conditional/refinement                  VALID" \
    "api_refinement/conditional/nonrefinement             INVALID" \
    "api_refinement/loop/refinement                         VALID" \
    "api_refinement/loop/nonrefinement                    INVALID" \
    "gni/nondet/leak                                      INVALID" \
    "gni/nondet/nonleak                                     VALID" \
    "gni/simple/leak                                      INVALID" \
    "gni/simple/nonleak                                     VALID" \
    "gni/smith/smith1                                     INVALID" \
    "gni/denning/denning1                                   VALID" \
    "gni/denning/denning2                                   VALID" \
    "param_usage/completely_unused/completely_unused      INVALID" \
    "param_usage/semantically_unused/semantically_unused  INVALID" \
    "param_usage/three_used/three_used                      VALID" \
    "param_usage/nondet_used/nondet_used                    VALID" \
    "param_usage/nondet_unused/nondet_unused              INVALID" \
)
fun_spec_file="./examples-java/src/main/java/utils/utils.jklspec"
retries=5
timeout_duration="20s"

stack build

pass_count=0
for elem in "${examples[@]}"; do
    read ex expected <<< "$elem"
    echo "Running $ex..."
    for ((i=0; i<retries; i++)); do
        output="$(timeout "$timeout_duration" \
                  stack exec java-orhle-exe -- \
                  "./examples-java/src/main/java/$ex.jklive" "$fun_spec_file" \
                  2> /dev/null \
                 )"; ec=$?
        if [[ $ec -eq 0 ]]; then
            break
        fi
        if [[ $ec -eq 124 ]]; then
            echo "timed out; retrying... ($i)"
        else
            echo "exited abnormally with $ec; retrying... ($i)"
        fi
    done
    if (( i == retries )); then
        echo "giving up on $ex"
    else
        if [[ "$output" == "$expected"* ]]; then
            echo "passed."
            (( pass_count++ ))
        else
            echo "***FAILED***"
        fi
    fi
done

echo "$pass_count / ${#examples[@]} examples passed"
