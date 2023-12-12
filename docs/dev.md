
# Development

## Project structure

- Hipcore: core language and spec AST and pure functions for manipulating it
- Provers: prover back ends which translate Hipcore types into SMT
- Hipprover: code which depends on calls to an external prover, e.g. normalization
- Ocamlfrontend: OCaml parser
- Hiplib: interface for all the above modules
- Hipjs, Hip: CLI and web frontends

[This file](../parsing/dune) lists the submodules of the various libraries. To see the structure graphically:

```sh
opam install dune-deps
dune-deps -x benchmarks -x src/programs.t | sed 's/\}/\{rank = same; "lib:provers_js"; "lib:provers_z3";\} \}/' | tred | dot -Tpng > deps.png
```

## Tests

`dune test` to run [tests](../src/programs.t/run.t).

Setting `TEST=1` causes the frontend to print only whether a test has failed.
A test is a function whose main entailment proof must succeed; if its name has the suffix `_false`, the entailment must fail.
We record the results for various interesting files using [cram tests](https://dune.readthedocs.io/en/stable/tests.html#cram-tests).

## Logging

View log output by setting `DEBUG=n`.

| n    | What                                 |
| ---- | ------------------------------------ |
| 0    | Results                              |
| 1    | Explanations, for users              |
| >= 2 | More and more detail, for developers |
