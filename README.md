# Heifer 

Heifer is an automated verification tool for 
effectful higher-order programs and 
algebraic effects and handlers. 

This README file serves for the artifact evaluation for the 
ICFP24 (#95) submission: 
**Specification and Verification for Unrestricted Algebraic Effects and Handling**. 


## Build Heifer 

We have a docker image to try out our tool, which is accessed from 
[Zenodo](https://link-url-here.org). 

The source code repository is placed in "/home/", called "AlgebraicEffect". 
The benchmarks are also summarized in the docker file, at "/home/AlgebraicEffect/src/demo/". 

Alternatively, one could build Heifer from scratch using a Linux system (tested on Ubuntu 22.04.4 LTS), with the following dependencies:

```
opam switch 5.0.0
apt install python3 dune menhir ppx_deriving ppx_expect brr js_of_ocaml-compiler unionFind visitors z3
npm install browserify -g 
dune build
dune test
```

Once successfully built, use `dune exec parsing/hip.exe $EXAMPLE` to run examples. 

## Reproduce Table 1

There are **eight** examples shown in Table 1, where each example 
has a reference for its implementation in the paper, either 
in the main text or in the appendix. 

As an example, to verify the first example, when running the following 
command: 
```
dune exec parsing/hip.exe src/demo/1_State_Monad.ml
```
the terminal eventually shows the following: 
```
========== FINAL SUMMARY ==========
[  LOC  ] 126
[  LOS  ] 16
[Forward+Entail+StoreSpec] 7.518679252 s
[ AskZ3 ] 5.47071003914 s
```
where "[LOC]" and "[LOS]" stand for lines of code and lines of specification, respectively; 
"[Forward+Entail+StoreSpec]" stands for the total execution time; 
and "[AskZ3]" stands for the time spent by the Z3 solver. 
Each of the items can find an correspondence in the Table. 

For the rest examples, the execution commands are summarized as follows: 
```
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

