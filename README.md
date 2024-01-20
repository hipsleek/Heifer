# Heifer

Heifer is a new verifier for effectful higher-order programs.

## Build

You will need OCaml 5.

```sh
opam install . --deps-only
```

Use `dune exec parsing/hip.exe $EXAMPLE` to run examples. Effect-related programs are in [src/evaluation](src/evaluation), higher-order programs are in [src/examples](src/examples).

## Docs

- [Development](docs/development.md)
- [Why3](docs/why3.md)



## SYH - Build

```
opam switch 5.0.0

brew install python3

opam install dune menhir ppx_deriving ppx_expect brr js_of_ocaml-compiler unionFind visitors z3

sudo npm install browserify -g # which browserify

dune build
dune test
```
