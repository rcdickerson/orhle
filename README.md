# ORHLE

ORHLE is an automatic existential relational Hoare logic (RHLE) verifier. The most recent draft of the RHLE paper is [available on arXiv](https://arxiv.org/abs/2002.02904).


### Building

Build, test, and run using [Stack](https://docs.haskellstack.org/en/stable/README):

```bash
stack build
stack exec orhle-exe <path-to-imp-file>
```

Building requires Z3 4.8.7 and its development headers. These packages are
available:
  * In many Debian-based Linux distributions as packages called `z3` and
    `libz3-dev`
  * As binaries from [the Z3 releases site](https://github.com/Z3Prover/z3/releases).
  * To build and install directly from [source](https://github.com/Z3Prover/z3).

### Experiments

Experiment benchmark code lives in the `experiments` directory.

Run all experiments using the `bin/run-experiments.sh` script. Per-benchmark
output is written to the `example-output` directory.

### Theory

The theories directory contains a Coq formalization of RHLE and the proofs presented
in Sections 2-4 of the paper.

* Run make to build everything.
* Coq 8.12.0 is required; although other versions may work as well.

Theorems from paper can be found in:
- Theorem 3.3: compatible_Env_refine in FunImp.v
- Theorem 3.5: rhle_proof_refine in Productive.v
- Theorem 4.4: rhle_proof_refine in RHLE.v
