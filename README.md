# RHLE Verifier

A proof-of-concept implementation of an existential relational hoare logic verification algorithm.
This project is still in an extremely nascent state.

### Building

Build, test, and run using [Stack](https://docs.haskellstack.org/en/stable/README):

```bash
stack build
stack exec rhle-verifier-exe
```

Executing as above will run the example hardcoded in `app/Main.hs`. To try other examples,
edit `Main.hs` or experiment in ghci by saying:

```bash
stack ghci
```

There is also a (currently somewhat minimal) test suite in the `test` directory. Tests
may be run with stack:

```bash
stack test
```

The test suite is also a good source for basic examples of valid and invalid triples.
