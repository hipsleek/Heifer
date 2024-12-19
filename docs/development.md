
# Development

## Project structure

**Libraries**
- Hipcore: core language and spec AST and pure functions for manipulating it
- Provers: prover back ends which translate Hipcore types into SMT
- Hipprover: code which depends on calls to an external prover, e.g. normalization
- Ocamlfrontend: OCaml parser

**Executables**
- Hiplib: interface for all the above modules
- Hipjs, Hip: CLI and web frontends

To see the structure of the project graphically:

```sh
opam install dune-deps
dune-deps -x benchmarks -x test/higher-order.t | sed 's/\}/\{rank = same; "lib:provers_js"; "lib:provers_native";\} \}/' | tred | dot -Tpng > deps.png
```

## Tests

`dune test` will run only unit tests, which are written inline in .ml files using [ppx_expect](https://github.com/janestreet/ppx_expect).

`TEST_ALL=1 dune test` will run slower integration tests. These use [cram](https://dune.readthedocs.io/en/stable/reference/cram.html) and may be found in `test/*.t/run.t`.
Individual suites of integration tests can be run using `TEST_ALL=1 dune build @higher-order`.

Some of the environment variables Heifer interprets may be useful for testing.

`PROVER=WHY3` or `PROVER=Z3` forces the use of the given prover. By default, the prover is chosen dynamically based on the verification task. Some tests pertain only to certain provers.

Setting `TEST=1` causes Heifer to print only whether a test has failed, which is useful for integration tests.
A test in this context is a function whose main entailment proof must succeed; if its name has the suffix `_false`, the entailment must fail.

## Logging and tracing

View log output by setting `DEBUG=n`.

| n    | What                                 |
| ---- | ------------------------------------ |
| 0    | Results                              |
| 1    | Explanations, for users              |
| >= 2 | More and more detail, for developers |

Set `FILE=1` to direct logs to an org-mode file, which is useful for structural navigation.

Set `CTF=1` to produce a trace file that can be viewed with [Perfetto](https://ui.perfetto.dev/), queried with [PerfettoSQL](https://perfetto.dev/docs/quickstart/trace-analysis), etc. This is useful for profiling.

## Testing programs using the old effect syntax

The old Multicore OCaml branch should work:

```sh
opam switch create 4.12.0+domains+effects
```

Otherwise, try [these instructions](https://github.com/ocaml/ocaml/blob/trunk/HACKING.adoc#testing-with-opam) with [this patch on top of OCaml 5.2](https://github.com/ocaml/ocaml/pull/12309).

```sh
opam switch create $SWITCH_NAME --empty
opam pin add ocaml-variants git+https://github.com/avsm/ocaml#effect-syntax
```

There are some differences. These modules need to be opened.

```ml
open Effect
open Effect.Deep
```

`Obj.clone_continuation` is also unavailable.

[ocaml-multicont](https://github.com/dhil/ocaml-multicont) can be used, but then it has a different API for continuations ("resumptions") and the old syntax won't be usable.