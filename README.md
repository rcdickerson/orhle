# ORHLE

## About the Archive

ORHLE is an automatic existential relational Hoare logic (RHLE)
verifier. It accepts programs written in the FunIMP language, a set of
universal and existential function specifications, and relational pre-
and post-conditions. (More detailed information on the input file
format is given [below](#Step-by-Step Instructions)). ORHLE attempts
to verify the pre- and post-conditions on the given FunIMP code and
reports either a) success or b) failure along with a falsifying model
if one was found.

ORHLE is written in Haskell and uses Z3 to discharge verification
conditions. Experiments were run on ORHLE compiled with GHC version
8.10.4 and executed against Z3 version 4.8.7. The accompanying
[Docker](https://www.docker.com/) image contains this version of Z3 as
well as an ORHLE binary built with the appropriate GHC version. GHC
itself is not included in the Docker image to reduce its size. The
image was built and tested with Docker version 20.10.17.


## Link To Research Paper

This is the accompanying artifact for the APLAS 2022 submission *RHLE:
Modular Deductive Verification of Relational ∀∃ Properties* by
Dickerson et al., and constitutes an implementation of the verification
algorithm given in Section 5 of that paper.

Section 6 of the paper poses the following three research questions:

* R1: Is RHLE expressive enough to represent a variety interesting properties?
  - This artifact supports this claim by providing a variety of properties
    in its benchmark suite.

* R2: Is our approach effective, that is, can it be used to verify or
  invalidate relational assertions about a diverse corpus of programs?
  - This artifact supports this claim by demonstrating ORHLE's
    ability to verify or invalidate the properties given in most
    of the experimental benchmarks.

* R3: Is it possible to realize an efficient implementation of our
  verification approach which return results within a reasonable time
  frame?
  - This artifact may not support this claim depending on the hardware
    on which the experiments are executed, although in our experimentation
    results were prompt.

The benchmark code is located in the `experiments` directory, and the
log files for our benchmark executions used to build Figure 7 in the
paper are located in the `experiments/_results` directory. (The
branching time property benchmarks, which were adapted from a
proprietary source, are not included in the public artifact.)
Benchmarks can be executed using the `bin/run-experiments.sh`
script as described [below](#Getting Started Guide).


## Getting Started Guide

This artifact is distributed as a [Docker]((https://www.docker.com/)
image; to use it, you will need to install the Docker Engine as
described in the [official Docker installation
instructions](https://docs.docker.com/engine/install/). The image was
created and this guide was written using Docker 20.10.17, but any
contemporary Docker version is expected to work. On *nix systems,
running `sudo docker run hello-world` is a quick way to check that
Docker is installed and behaving correctly.

Once Docker Engine is installed, you need to load the ORHLE
image in one of the following ways:

* If you have obtained the ORHLE Docker image as a tar archive, you
  can load it with: `# docker load < orhle.tar.gz`

* If you do not have the image, you can pull it from Docker Hub:
  `# docker pull rcdickerson/orhle:aplas2022`

* You can obtain the ORHLE source code and build the Docker image
  yourself:
  ```bash
  $ git clone https://github.com/rcdickerson/orhle.git
  $ cd orhle
  $ git checkout aplas2022
  # docker build --tag rcdickerson/orhle:aplas2022
  ```

After loading the ORHLE image in one of these ways, you should
see it in the output of `docker images`, for example:

```bash
# docker images
REPOSITORY          TAG         IMAGE ID       CREATED         SIZE
rcdickerson/orhle   aplas2022   07a6627f6f18   4 hours ago     545MB
```

### Running a Single Benchmark

Benchmarks are located in the `examples` directory. For example,
to run the average salaries benchmark in the delimited release
benchmarks:

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

Experiment benchmark code lives in the `experiments` directory. Data
in the paper was generated using the `bin/run-experiments.sh` script.
When running this script, per-benchmark output is written to the
`experiments\_results` directory.

You can execute `run-experiments` inside the Docker container by
setting it to be the entry point:

```bash
# docker run --entrypoint bin/run-experiments.sh rcdickerson/orhle:aplas2022
```

When running the script, you should see a summary of the benchmark
executions. Detailed execution logs are written to
`experiments/_results` which you can view by shelling in to the
container:

```bash
# docker run -it --entrypoint bash rcdickerson/orhle:aplas2022
# cd experiments/_results
```

or mounting it as a [Docker volume](https://docs.docker.com/storage/volumes/).


### Building ORHLE with Stack

ORHLE uses the [Stack](https://docs.haskellstack.org/en/stable/README)
build tool. To build ORHLE, simply execute `stack build` or `stack
install` from the project's root directory. The executable takes
as argument a single `.imp` file. You can either run the executable
generated by Stack directly, or can use Stack to execute ORHLE:

```bash
$ stack build
$ stack exec orhle-exe <path-to-imp-file>
```

Building ORHLE requires Z3 4.8.7 and its development headers. These
packages are available:
  * In many Debian-based Linux distributions as packages called `z3` and
    `libz3-dev`
  * As binaries from [the Z3 releases site](https://github.com/Z3Prover/z3/releases).
  * To build and install directly from [source](https://github.com/Z3Prover/z3).


### The ORHLE Input File Format

ORHLE input files are formatted as follows:

```
expected: <expect>;

forall: <funName>*
exists: <funName>*

pre: <smtlib2>
post: <smtlib2>

aspecs: <aspec>*
especs: <espec>*

<funDef>*
```

where:
+ `<expect> ::= valid | invalid` indicates whether the file is
  expected to verify. The `expected` tag is optional and entirely for
  bookkeeping purposes; it has no operational effect on the execution
  of ORHLE.
+ `<funName> ::= <string>([<string>])?` is the name of a FunIMP
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
+ `<aspec> ::= <funName>(<params>) { pre: <smtlib2>; post: <smtlib2>;
  }` gives a universal specification for its `funName`. The `pre` and
  `post` specifications may reference any program state and the
  function parameters. Additionally, the postcondition can reference
  the special variable `ret!` to refer to the function's return value.
+ `<espec> ::= <funName>(<params>) { choiceVars: <string>*; pre:
  <smtlib2>; post: <smtlib2>; }` gives an existential specification for
  its `funName`, where `choiceVars` is a list of choice variable
  names that may be referenced in the `pre` and `post` conditions.
+ `<funDef> ::= fun <funName>(<params>) { <FunIMP> }` is a function
  definition. `<FunIMP>` is FunIMP syntax as given in Figure 2 of
  the paper. At the time of writing, loops must be decorated
  with invariants given as `@inv { <smtlib2> }`. Loops in existential
  executions must also be decorated with variants given as `@var {
  <smtlib2> }`
+ `<params>` is a comma-separated list of strings giving function
  parameter names.

See the `experiments` directory for a variety of example ORHLE input files.


## Theory

The `theories` directory contains a Coq formalization of the program
logics from the paper. We executed these proof scripts using Coq
8.15.2, but other versions may work as well.

To build all theories, run `make` from the `theories` directory:

```bash
$ cd theories
$ make
```

The key definitions and theorems are as follows:

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
