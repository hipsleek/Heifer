
# Development

## Project structure

**Libraries**
- Debug: Helpers for debug logging
- Hipcore: core language and spec AST and pure functions for manipulating it
- Hipcore_typed: core language and spec AST with type annotations
- Hipcore_common: libraries and definitions common to both the untyped and typed ASTs
- Provers: prover back ends which translate Hipcore types into SMT
- Hipprover: code which depends on calls to an external prover, e.g. normalization
- Ocamlfrontend: OCaml parser
- Parsing: parsing for specifications

**Executables**
- Hiplib: interface for all the above modules
- Hipjs, Hip: CLI and web frontends

To see the structure of the project graphically:

```sh
opam install dune-deps
dune-deps -x benchmarks -x test/higher-order.t | sed 's/\}/\{rank = same; "lib:provers_js"; "lib:provers_native";\} \}/' | tred | dot -Tpng > deps.png
```

## Pipeline

### Parsing and typechecking

`Core_lang_typed` does most of the work in converting the OCaml typedtree into the core language. The translation process also carries over types.
A type inference engine in `Hipprover.Infer_types` is used to fill in the remaining types, e.g. of terms found in specifications.

### Entailment checking

Forward verification is first performed on the core language expression to obtain a specification that describes the code as written. The logic for doing so
can be found in `Hipprover.Forward_rules`. This specification is then checked to see if it entails the user-provided specification, if present.

The main entry point for the entailment checking procedure is `Entail.check_staged_spec_entailment`, which attempts to prove that one specification entails another. It attempts to apply a list of tactics one by one,
repeatedly, in order to match up the stages in both specifications.

After applying each tactic, normalization rules are applied to the specification; the set of rules can be found in `Normalize`. Normalization rules specific to handling shift/reset-related stages
can be found in `Reduce_shift_reset`.

Most formula manipulation tasks (e.g. applying a rewriting rule, unfolding a predicate) are handled by one of two rewriting systems:

- `Rewriting` is based on _unification variables_, which can be matched with and substituted for by other AST nodes representing actual values, stages, etc. This
is currently used to implement lemma and predicate instantiation.
- `Rewriting2` is based on `Ppxlib`'s `Ast_pattern`, and is suited for rules that are statically known (i.e. the pattern to match
does not depend on the program being proved).

### Discharging to SMT

Before discharging pure logic formulas to SMT, some simplification of terms is performed. The simplification rules can be found in `Simpl`.

Currently, the web frontend uses Z3, while the CLI backend uses either Why3 or Z3. (See the Tests section for
how the specific backend is chosen.)

The entailment checker can be found in `Provers`. It accepts queries of the form `A => ex x1, x2, .., xn. B`, and returns either `Valid`,
`Invalid`, or `Unknown` (with an explanation in case of the last case).

## Tests

`dune test` will run only unit tests, which are written inline in .ml files using [ppx_expect](https://github.com/janestreet/ppx_expect).

`TEST_ALL=1 dune test` will run slower integration tests. These use [cram](https://dune.readthedocs.io/en/stable/reference/cram.html) and may be found in `test/*.t/run.t`.
Individual suites of integration tests can be run using `TEST_ALL=1 dune build @higher-order`.
To run one test, `TEST_ALL=1 dune build @higher-order`.

Some of the environment variables Heifer interprets may be useful for testing.

`PROVER=WHY3` or `PROVER=Z3` forces the use of the given prover. By default, the prover is chosen dynamically based on the verification task. Some tests pertain only to certain provers.

Setting `TEST=1` causes Heifer to print only whether a test has failed, which is useful for integration tests.
A test in this context is a function whose main entailment proof must succeed; if its name has the suffix `_false`, the entailment must fail.

## Untyped extensions

Some extensions not supported by mainline OCaml are supported. Currently, this only includes delimited continuation operators (ala [OchaCaml](https://www.is.ocha.ac.jp/~asai/OchaCaml/)), but more may be supported.

Setting `NOTYPES=1` will defer all typechecking during entailment checks until necessary (i.e. before SMT translation). This may be useful to ease development of extensions
outside of those typechecked by OCaml.

## Logging and tracing

View log output by setting `DEBUG=n`.

| n    | What                                 |
| ---- | ------------------------------------ |
| 0    | Results                              |
| 1    | Explanations, for users              |
| >= 2 | More and more detail, for developers |

Several built-in filtering options are available; these can be set by setting `DEBUG='n; <option 1>; <option 2>; ...`. See the documentation of `debug.mli` for more details.

Some helpful options:
- `h rewrite_*` filters out all logs related to the rewrite libraries (which appear at level 5 and above).
- `h unify_types; h infer_types*` filters out all logs related to type inference (which appear at level 10 and above).

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
