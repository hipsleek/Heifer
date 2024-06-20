# FM24 Artifact Evaluation

This README is meant to guide artifact evaluation for FM24 paper 28:
**Staged Specification Logic for Verifying Higher-Order Imperative Programs**.

## Abstract

This artifact comprises the source code of Heifer, an automated verification tool based on the logic presented in Sections 2-5 of the paper, as well as everything required (scripts, input programs, Dockerfile) to run the experiments described in Section 6 of the paper.

## Building Heifer 

We have a docker image to try out our tool, which can be accessed from 
[Zenodo](https://link-url-here.org). 

```
docker pull dariusf/heifer-icfp24
docker run -it --rm dariusf/heifer-icfp24 /bin/bash
```


The source code repository is placed in "/home/AlgebraicEffect". 
The benchmarks are also summarized in the docker file, at "/home/AlgebraicEffect/src/demo/". 

To test build, one can use the following command. 
When you run it, if there are no errors, you know it builds correctly. 
```
dune build parsing/hip.exe 
```


To build Heifer from scratch, the same [Dockerfile](Dockerfile) used to build the above image is provided together with the source code, and may be used or consulted.

Once successfully built, we could use `dune exec parsing/hip.exe $EXAMPLE` to run examples. 

## Reproduce Table 1

Table 1 shows 8 examples, each referencing its implementation in the paper, either in the main text or the appendix. 

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

Here, "[LOC]" and "[LOS]" stand for lines of code and lines of specifications, respectively; "[Forward+Entail+StoreSpec]" stands for the total verification time; and "[AskZ3]" stands for the time spent by the Z3 solver. 
Each of these items corresponds to a specific entry in the table. 

For the correctness checking, one should look at the verification results for each function. See an example below, where "[Entail  Check]" stands for the success of the verification. 

```
========== Function: read ==========
[Specification] ex ret; Read(emp, (), ret); ens res=ret/\T
[Normed   Spec] ex ret; Read(emp, (), ret); ens res=ret
[Normed   Post] ex v1; Read(emp, (), v1); ens res=v1

[Forward  Time] 29 ms
[Entail  Check] true
[Entail   Time] 57 ms
[Z3       Time] 72 ms
====================================
```

There are cases where the results do not contain the "[Entail Check]" entry, such as the following example. This is because there are no specifications provided for this function; thus, Heifer makes inferences for its specifications, as shown in the "[Normed Post]" entry. 

```
========== Function: test1 ==========
[Normed   Post] ex v1253; Read(emp, (), v1253); ex v1239 v1252; Write(v1239=(v1253+1), (v1239), v1252); ex v1251; Read(emp, (), v1251); ex v1246 v1250; Write(v1246=(v1251+1), (v1246), v1250); ex v1248; Read(emp, (), v1248); ens res=v1248

[Forward  Time] 171 ms
[Z3       Time] 154 ms
=====================================
```

Almost all the functions in the example files should verify, i.e., [Entail  Check] shows *true*, except for "8_schduler.ml", detailed later. 
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

In the last example, "8_schduler.ml", three functions do not verify: queue_push, queue_is_empty and queue_pop. 
This is OK because we take their specifications as  axioms, and with these assumptions, this example 
aims to verify the "spawn" function. More explanations for this example can be found in Appendix C.0.5. 



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

## Building the Docker image

```sh
docker build -t heifer-fm24 -f Dockerfile . --progress=plain
docker run -it heifer-fm24 bash
```
