
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
dune-deps -x benchmarks -x src/programs.t | sed 's/\}/\{rank = same; "lib:provers_js"; "lib:provers_native";\} \}/' | tred | dot -Tpng > deps.png
```

## Tests

`dune test` to run [tests](../src/programs.t/run.t).

Setting `TEST=1` causes the frontend to print only whether a test has failed.
A test is a function whose main entailment proof must succeed; if its name has the suffix `_false`, the entailment must fail.
We record the results for various interesting files using [cram tests](https://dune.readthedocs.io/en/stable/tests.html#cram-tests).

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