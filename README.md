# ORHLE

ORHLE is an automatic existential relational Hoare logic (RHLE) verifier. The most recent draft of the RHLE paper is [available on arXiv](https://arxiv.org/abs/2002.02904).


### Building

Build, test, and run using [Stack](https://docs.haskellstack.org/en/stable/README):

```bash
stack build
stack exec klive-exe
```

Building requires Z3 4.8.7 and its development headers. Some ways of getting this:
  * In many Debian-based Linux distributions the packages called `z3` and
    `libz3-dev` (so, `apt-get install z3 libz3-dev`)
  * Get the binaries from [the Z3 releases site](https://github.com/Z3Prover/z3/releases)
  * Build and install Z3 directly from [source](https://github.com/Z3Prover/z3)


### Examples

Example encodings live in the `examples` directory.

You can run single examples using the `bin/run-example.sh` script. For example:

```bash
bin/run-example.sh api-refinement add3-shuffled
```

will run `examples/api-refinement/add3-shuffled.imp` and write output to the
console, as well as to `example-output/api-refinement/add3-shuffled.out`.

Saying:

```bash
bin/run-all-examples.sh
```

will run all examples, writing output to the `example-output` directory.

