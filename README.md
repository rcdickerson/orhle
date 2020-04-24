# ORHLE

ORHLE is an automatic existential relational Hoare logic (RHLE) verifier. A
draft of the RHLE paper is currently on arXiv: https://arxiv.org/abs/2002.02904

### Building

Build, test, and run using [Stack](https://docs.haskellstack.org/en/stable/README):

```bash
stack build
stack exec klive-exe
```

### Examples

Example encodings live in the `examples` directory.

You can run single examples using the `bin/run-example.sh` script. For example:

```bash
bin/run-example.sh api-refinement add3-shuffled
```

will run `examples/api-refinement/add3-shuffled.imp` and write output to the
console, as well as to `examples/orhle-output/api-refinement/add3-shuffled.out`.

Saying:

```bash
bin/run-all-examples.sh
```

will run all examples, writing output to `examples/orhle-output`.
