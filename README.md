# ORHLE

ORHLE is an automatic existential relational Hoare logic (RHLE) verifier. The most recent draft of the RHLE paper is [available on arXiv](https://arxiv.org/abs/2002.02904).


### Building

Build, test, and run using [Stack](https://docs.haskellstack.org/en/stable/README):

```bash
stack build
stack exec orhle-exe <path-to-imp-file>
```

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
