# Heifer 

Heifer is an automated verification tool for 
effectful higher-order programs and 
algebraic effects and handlers. 

This README file serves for the artifact evaluation for the 
ICFP24 (#95) submission: 
**Specification and Verification for Unrestricted Algebraic Effects and Handling**. 


## Build Heifer 

We have a docker image to try out our tool, which is detailed in the 

```
docker pull yahuuuuui/icfp24-heifer:ubuntu
docker run -i -t yahuuuuui/fse24-heifer:ubuntu /bin/bash
```

The source code repository is placed in "/home/", called "AlgebraicEffect". 
The benchmarks are also summarized in the docker env. 
Alternatively, one could build \toolName from scratch using a Linux system (tested on Ubuntu 22.04.4 LTS), with the following dependencies:

```
opam switch 5.0.0
apt install python3 dune menhir ppx_deriving ppx_expect brr js_of_ocaml-compiler unionFind visitors z3
npm install browserify -g 
which browserify
dune build
dune test
```

Use `dune exec parsing/hip.exe $EXAMPLE` to run examples. Effect-related programs are in [src/evaluation](src/evaluation), higher-order programs are in [src/examples](src/examples).

## Reproduce Table 1

```
dune exec parsing/hip.exe src/demo/1_State_Monad.ml
dune exec parsing/hip.exe src/demo/2_Inductive_Sum.ml
dune exec parsing/hip.exe src/demo/3_Deep_Right_Toss.ml
dune exec parsing/hip.exe src/demo/4_Deep_Left_Toss.ml
dune exec parsing/hip.exe src/demo/5_Shallow_Right_Toss.ml
dune exec parsing/hip.exe src/demo/6_Shallow_Left_Toss.ml
dune exec parsing/hip.exe src/demo/7_amb.ml
dune exec parsing/hip.exe src/demo/8_schduler.ml
```



## Docs

- [Development](docs/development.md)
- [Why3](docs/why3.md)
- [How the web build works](docs/web.md)
- [Docker packaging](docs/docker.md)

