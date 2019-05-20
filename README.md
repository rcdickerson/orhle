# RHLE Verifier

A proof-of-concept implementation of an existential relational hoare logic verification algorithm.
This project is still in an extremely nascent state.

### Building

Build and run using [Stack](https://docs.haskellstack.org/en/stable/README):

```bash
stack build
stack exec rhle-verifier-exe
```

Executing as above will run the example hardcoded in `app/Main.hs`. To try other examples,
edit `Main.hs` or experiment in ghci by saying:

```bash
stack ghci
```
