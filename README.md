# Heifer 

Heifer is an automated verification tool for 
effectful higher-order programs and 
algebraic effects and handlers. 

This README file serves for the artifact evaluation for the 
ICFP24 (#95) submission: 
**Specification and Verification for Unrestricted Algebraic Effects and Handling**. 


## Build Heifer 

We have a docker image to try out our tool, which is detailed in the 

```sh
docker pull yahuuuuui/heifer-icfp24:latest
docker run -it --rm yahuuuuui/heifer-icfp24:latest bash
```

The source code repository is placed in `/home/opam/AlgebraicEffect`. 
The benchmarks are also summarized in the docker env. 

To build Heifer from scratch, the same Dockerfile used to build the above image is provided together with the source code, and may be used or consulted.

<!--
Alternatively, one could build Heifer from scratch using a Linux system (tested on Ubuntu 22.04.4 LTS), with the following dependencies:

```
opam switch 5.0.0
apt install python3 dune menhir ppx_deriving ppx_expect brr js_of_ocaml-compiler unionFind visitors z3
npm install browserify -g 
which browserify
dune build
dune test
```
-->

Use `heifer $EXAMPLE` to run examples.

<!-- Effect-related programs are in [src/evaluation](src/evaluation), higher-order programs are in [src/examples](src/examples). -->

## Reproduce Table 1

```sh
heifer src/demo/1_State_Monad.ml
heifer src/demo/2_Inductive_Sum.ml
heifer src/demo/3_Deep_Right_Toss.ml
heifer src/demo/4_Deep_Left_Toss.ml
heifer src/demo/5_Shallow_Right_Toss.ml
heifer src/demo/6_Shallow_Left_Toss.ml
heifer src/demo/7_amb.ml
heifer src/demo/8_schduler.ml
```


## Project structure

The source code is in the `parsing` directory.
The project builds with dune, and the `dune` file in that directory contains a listing of the project's components.
A brief description of the relevant ones:

- hip: entry point
- ocamlfrontend: part of the OCaml 4.12 compiler frontend, modified to parse the `(*@ comments @*)` used for writing ESL specifications
- hipcore: AST for staged/separation logic/pure formulae and operations such as pretty-printing, substitution, etc.
- hipprover: the entailment prover for staged formulae, which consists of modules for applying the forward rules, applying lemmas, proof search, biabduction-based normalization, and entailment checking

## Docs

- [Development](docs/development.md)
- [Why3](docs/why3.md)
- [How the web build works](docs/web.md)
- [Docker packaging](docs/docker.md)

