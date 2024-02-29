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
- [How the web build works](docs/web.md)


## SYH - Build

```
opam switch 5.0.0

brew install python3

opam install dune menhir ppx_deriving ppx_expect brr js_of_ocaml-compiler unionFind visitors z3

sudo npm install browserify -g 

which browserify

dune build
dune test
```

```
cd parsing 
ocamllex lexer.mll
menhir parser.mly 

dune exec parsing/hip.exe src/evaluation/0_heap_zero_once_twice.ml

```

dune exec parsing/hip.exe src/demo/1_State_Monad.ml
dune exec parsing/hip.exe src/demo/2_Inductive_Sum.ml
dune exec parsing/hip.exe src/demo/3_Deep_Right_Toss.ml
dune exec parsing/hip.exe src/demo/4_Deep_Left_Toss.ml
dune exec parsing/hip.exe src/demo/5_Shallow_Right_Toss.ml
dune exec parsing/hip.exe src/demo/6_Shallow_Left_Toss.ml
dune exec parsing/hip.exe src/demo/7_amb.ml
dune exec parsing/hip.exe src/demo/8_schduler.ml


