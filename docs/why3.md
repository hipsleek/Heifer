
# The Why3 backend (experimental)

```sh
opam update 
# Install dependencies, which includes the Why3 IDE
opam install . --deps-only

# Install some provers (optional)
which z3 # already installed
opam install alt-ergo
brew install cvc4

# Configure why3
why3 config detect

# Run examples and tests
PROVER=WHY3 dune exec parsing/hip.exe $EXAMPLE
PROVER=WHY3 dune test
```