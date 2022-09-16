# Ceili

Fancy stepping through program syntax.


### Building

Build the library via [Stack](https://docs.haskellstack.org/en/stable/README/):

```
stack build
```


### Testing

Tests are divided into quick-running unit tests, which you may run like:

```
stack test ceili:ceili-test
```

and longer-running end-to-end verification tests, which you may run like:

```
stack test ceili:ceili-verification-test
```

Saying `stack test` will run both test suites.

You can select individual tests to run with the `--test-arguments` switch.
For example, the following command will run the `loopInvGen` tests in the
verification suite:

```
stack test ceili:ceili-verification-test --test-arguments="loopInvGen"
```
