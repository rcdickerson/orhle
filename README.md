# ORHLE

## About the Archive

ORHLE is an automatic verifier for relational Hoare logic with
existentials (RHLE). It accepts programs written in the FunIMP
language (details on the input file format are given below) and
attempts to verify relational pre- and post-conditions. The outcome of
an ORHLE verification attempt is either success or failure along with
a falsifying model.

ORHLE is written in Haskell and uses Z3 to discharge verification
conditions. We ran experiments on ORHLE compiled with GHC version
8.10.4 and executed against Z3 version 4.8.7. The accompanying
[Docker](https://www.docker.com/) image contains the above version of
Z3 as well as an ORHLE binary built with the above GHC version. GHC
itself is not included in the Docker image to reduce the size of the
image. The image was built and tested with Docker version 20.10.17.


## Link To Research Paper

This is the accompanying artifact for the APLAS 2022 submission *RHLE:
Modular Deductive Verification of Relational ∀∃ Properties* by
Dickerson et al., and constitutes an implementation of the verification
algorithm given in Section 5 of that paper.

Section 6 of the paper poses the following three research questions:

* R1: Is RHLE expressive enough to represent a variety of interesting
  properties?
  - This artifact supports this claim by providing a variety of properties
    in its benchmark suite.

* R2: Is our approach effective, that is, can it be used to verify or
  invalidate relational assertions about a diverse corpus of programs?
  - This artifact supports this claim by demonstrating ORHLE's
    ability to verify or invalidate the properties given in most
    of the experimental benchmarks.

* R3: Is it possible to realize an efficient implementation of our
  verification approach which returns results within a reasonable time
  frame?
  - This artifact may not support this claim depending on the hardware
    on which the benchmarks are executed. In our evaluation, results
    were prompt.

The benchmark code is located in the `experiments` directory, and the
log files for our benchmark executions used to build Figure 7 are
located in the `experiments/_results` directory. (The branching time
property benchmarks, which were adapted from a proprietary source, are
not included in the public artifact.) Benchmarks can be executed using
the `bin/run-experiments.sh` script as described below.


## Getting Started Guide

This artifact is distributed as a [Docker](https://www.docker.com/)
image. To use it, you will need to install the Docker Engine as
described in the [official Docker installation
instructions](https://docs.docker.com/engine/install/). The image was
created and this guide was written using Docker 20.10.17, but any
contemporary Docker version is expected to work. On *nix systems,
running `sudo docker run hello-world` is a quick way to check that
Docker is installed and behaving correctly.

Once Docker Engine is installed, you need to load the ORHLE
image in one of the following ways:

* If you have obtained the ORHLE Docker image as a tar archive, you
  can load it directly:
  ```bash
  # docker load < orhle.tar.gz
  ```

* You can pull the image from Docker Hub:
  ```bash
  # docker pull rcdickerson/orhle:aplas2022
  ```

* You can obtain the ORHLE source code and build the Docker image
  yourself:
  ```bash
  $ git clone https://github.com/rcdickerson/orhle.git
  $ cd orhle
  $ git checkout aplas2022
  # docker build --tag rcdickerson/orhle:aplas2022 .
  ```

After loading the ORHLE image in one of these ways, you should
see it in the output of `docker images`, for example:

```bash
# docker images
REPOSITORY          TAG         IMAGE ID       CREATED         SIZE
rcdickerson/orhle   aplas2022   07a6627f6f18   4 hours ago     545MB
```

### Running a Single Benchmark

You can run ORHLE with `docker run`, providing a `.imp` file to
verify. (This file format is described in more detail below.)
Benchmark `.imp` files evaluated in the paper are located in the
`experiments` directory. To execute the average salaries delimited
release benchmark, for example, execute:

```bash
# docker run \
  rcdickerson/orhle:aplas2022 \
  experiments/delimited-release/avg-salaries.imp
```

You should see a summary of the verification task and
a response of `Valid`.

The `avg-salaries-no-dr` benchmark is the same code without the
delimited release condition:

```bash
# docker run \
  rcdickerson/orhle:aplas2022 \
  experiments/delimited-release/avg-salaries-no-dr.imp
```

Here, you should see a `Failure` response along with a falsifying
model.


## Step-by-Step Instructions

### Running all Benchmarks

Experiment benchmark code lives in the `experiments` directory.
Evaluation data in the paper were generated using the
`bin/run-experiments.sh` script. When running this script,
per-benchmark output is written to the `experiments/_results`
directory.

You can execute `run-experiments` inside the Docker container:

```bash
# docker run -it --entrypoint bash rcdickerson/orhle:aplas2022
# bin/run-experiments.sh
```

Detailed execution logs are written to `experiments/_results`. You can
access results from any ORHLE image by mounting it as a [Docker
volume](https://docs.docker.com/storage/volumes/). The ORHLE Docker
image contains the experimental results presented in the paper in its
`experiments/_results` directory.


### Building ORHLE with Stack

ORHLE uses the [Stack](https://docs.haskellstack.org/en/stable/README)
build tool. To build ORHLE, execute `stack build` or `stack install`
from the project's root directory. The executable takes as an argument
a single `.imp` file. You can either run the executable generated by
Stack directly, or use Stack to execute ORHLE:

```bash
$ stack build
$ stack exec orhle-exe <path-to-imp-file>
```

Building ORHLE requires Z3 4.8.7 and its development headers. These
packages are available:
  * In many Linux distributions as packages called `z3` and
    `libz3-dev`, respectively.
  * As binaries from [the Z3 releases site](https://github.com/Z3Prover/z3/releases).
  * To build and install directly from [source](https://github.com/Z3Prover/z3).


### The .imp File Format

ORHLE input files are formatted as follows:

```
expected: <expect>;

forall: <execName>*
exists: <execName>*

pre: <smtlib2>
post: <smtlib2>

aspecs: <aspec>*
especs: <espec>*

<funDef>*
```

where

+ `<expect> ::= valid | invalid` indicates whether the file is
  expected to verify. The `expected` tag is optional and entirely for
  bookkeeping purposes; it has no operational effect on the execution
  of ORHLE.
+ `<execName> ::= <string>([<string>])?` is the name of a FunIMP
  function defined later in the file optionally annotated with an
  execution identifier. The execution identifier distinguishes
  between different executions of the same function. For example,
  a single function `foo` appearing on both the ∀ and ∃ sides
  of a RHLE triple might be given as:
  ```
  forall: foo[A]
  exists: foo[E]
  ```
+ `<smtlib2>` represents a specification given as an SMTLib2 string.
  Variables inside functions are referenced by using `!` as a
  separator; for example, if function `foo` has a variable `x`, SMTLib
  specifications can refer to the value as `foo!x`. If a function
  as multiple executions, the execution ID should appear after
  the function name separated by `!`; for example, value `x`
  in `foo[A]` should be referred to as `foo!A!x`.
+ `<aspec> ::= <string>(<params>) { pre: <smtlib2>; post: <smtlib2>;
  }` gives a universal specification for some function. The `pre` and
  `post` specifications may reference any program state and the
  function parameters. Additionally, the postcondition can reference
  the special variable `ret!` to refer to the function's return value.
+ `<espec> ::= <string>(<params>) { choiceVars: <string>*; pre:
  <smtlib2>; post: <smtlib2>; }` gives an existential specification
  for some function, where `choiceVars` is a list of choice variable
  names that may be referenced in the `pre` and `post` conditions.
+ `<funDef> ::= fun <string>(<params>) { <FunIMP> }` is a function
  definition. `<FunIMP>` is FunIMP syntax as given in Figure 2 of
  the paper. At the time of writing, loops must be decorated
  with invariants given as `@inv { <smtlib2> }`. Loops in existential
  executions must also be decorated with variants given as `@var {
  <smtlib2> }`
+ `<params>` is a comma-separated list of strings giving function
  parameter names.

See the `experiments` directory for a variety of example ORHLE input
files.


## Theory

The `theories` directory contains a Coq formalization of the program
logics from the paper. We executed these proof scripts using Coq
8.15.2, but other versions may work as well.

### Obtaining Coq

The standard ORHLE Docker image does not contain Coq to reduce the
size of the image. However, a "full" version of the image is
available on Dockerhub:

```bash
# docker pull rcdickerson/orhle:aplas2022-full
```

You can also build the full image by using the `.full` version
of the Dockerfile:

```bash
$ git clone https://github.com/rcdickerson/orhle.git
$ cd orhle
$ git checkout aplas2022
# docker build -f Dockerfile.full --tag rcdickerson/orhle:aplas2022-full .
```

If you are using the "full" version of the ORHLE image, the correct
version of Coq is present and you can build the theories directly
within the image:

```bash
# docker run -it --entrypoint bash rcdickerson/orhle:aplas2022-full
# cd theories
# eval $(opam env) && make
```

If you are using the standard ORHLE image, Coq is not included and you
will need to install it to build the theories. Instructions for
installing Coq Platform with Coq 8.15.2 can be found in the
[Coq Platform documentation](
https://github.com/coq/platform/blob/main/doc/README~8.15~2022.04.md).
After installing Coq, you can obtain the theory files either via
[Github]( https://github.com/rcdickerson/orhle.git) or by mounting the
ORHLE image as a [volume](https://docs.docker.com/storage/volumes/).

### Key Definitions and Theorems

- The syntax (Figure 2, page 3), semantics (Figure 8, page 21), and
  overapproximate executions (Figure 9, page 22) of FunImp can be found
  in FunImp.v. The current semantics uses both an implementation and
  universal specification context. The ECall_forall rules require that
  no function definition is available in the implementation context.

- The Coq definition of compatibility (Definition 1, page 4) is named
  `compatible_env` and can be found in FunImp.v.

- The Coq proof of Theorem 1 (page 5) is named `compatible_Env_refine`
  and can be found in FunImp.v.

- The Coq definition of existential executions (Figure 4, page 7)
  is named `ceval_Ex` and can be found in Productive.v.

- The Coq definition of compatibility (Definition 2, page 5),
  `ex_compatible_env`, can be found in Productive.v.

- The Coq proof of Theorem 2 (page 6) is named `productive_refine` and
  can be found in Productive.v.

- The Coq definition of the universal Hoare proof rules (Figure 10, page 23)
  is named `hoare_proof` and can be found in Hoare.v.

- The Coq definition of the existential Hoare proof rules (Figure 11, page 24)
  is named `hle_proof` and can be found in HLE.v.

- The Coq definition of the Core RHLE proof rules (Figure 6, page 9)
  is named `rhle_proof` and can be found in RHLE.v.

- The Coq proof of soundness for the Core RHLE proof rules, page 11)
  is named `rhle_proof_refine` and can be found in RHLE.v.

- The Coq definition of the core + synchrnous RHLE proof rules (Figure
  6, page 9; SyncLoops rule, page 11 ) is named `rhle_proof` and can
  be found in RHLE2.v.

- The Coq proof of soundness for the core + synchronous RHLE proof
  rules (Theorem 3, page 11) is named `rhle_proof_refine` and can be
  found in RHLE2.v.
