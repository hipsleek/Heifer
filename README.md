# FM24 Artifact Evaluation

This README is meant to guide artifact evaluation for FM24 paper 28:
**Staged Specification Logic for Verifying Higher-Order Imperative Programs**.

## Abstract

Our artifact is a self-contained Docker image which contains the source code of Heifer, an automated verification tool based on the logic presented in Sections 2-5 of the paper, as well as the scripts and inputs required to run the experiments described in Section 6 of the paper.

## Running the artifact

After downloading the artifact from Zenodo and making it available as heifer-fm24.tgz, it may be run as follows.

```sh
docker load -i heifer-fm24.tgz
docker run -it --rm heifer-icfp24 /bin/bash
```

You should see the following before the shell prompt appears.

```
[Artifact of FM #28: Heifer]
To reproduce the paper's experiments, run benchmarks/ho/experiments.py
Further details may be found in README.md (vim and nano are pre-installed).
```

To check that everything is set up correctly:

```sh
# check if Heifer is built
dune build parsing/hip.exe && echo OK
# should print OK all is well

# run a test
TEST=1 dune exec parsing/hip.exe src/examples/fold.ml
# should print "ALL OK!" if all is well
```

## Structure of the artifact

The source code is in `/home/AlgebraicEffect` (where the user should find themselves after entering a shell).

The benchmarks mentioned in Section 6 are in `/home/AlgebraicEffect/benchmarks/ho`. 

## Running individual benchmark programs

The benchmark programs may be run individually as follows.

```sh
dune exec parsing/hip.exe benchmarks/ho/heifer/map.ml
```

A record like this is printed for each function in the input file.

```
========== Function: map_id ==========
[ Specification ] ens res=ys

[  Normed Spec  ] ens res=ys

[ Raw Post Spec ] ens emp; ex v23; map(id, ys, v23); ens res=v23

[  Normed Post  ] ex v23; map(id, ys, v23); ens res=v23

[  Entail Check ] true

[  Forward Time ] 0 ms
[   Norm Time   ] 6 ms
[  Entail Time  ] 14 ms
[    Z3 Time    ] 14 ms
[   Why3 Time   ] 0 ms
[  Overall Time ] 18 ms
======================================
```

- Specification/Normed Spec: the user-provided specification for this function, before and after normalization (Section 3.2)
- Raw Post Spec/Normed Post: the strongest postcondition of the function (Section 4), before and after normalization
- Entail Check: true iff the computed postcondition entails the given specification (section 5)
- Forward, Entail Time: the time taken by each of these phases
- Norm Time: the time spent performing normalization, which may occur during both phases
- Z3, Why3 Time: the time spent in each of these provers, which may be called by both phases and by normalization
- Overall Time: the wall-clock time taken to verify this function

For some functions, the result does not contain "Entail Check" entry.
This is because a user-provided specification is not given, so no verification takes place.
The strongest postcondition is still computed and is used as the specification for subsequent calls to this function.

## Reproducing experiments

To reproduce the experiments in Section 6 of the paper, execute the following script.

```sh
benchmarks/ho/experiments.py
```

This runs Heifer on all 13 benchmark programs mentioned in Table 1 and measures how long verification takes.

An example of what output should look like is as follows.

```
Running benchmarks...
map
[names of other benchmarks]

----------

Benchmark: map
LoC: 13
LoS: 11
Total time: 0.13
Prover time: 0.09

[similar blocks for other benchmarks]

----------

[statistics about benchmark sizes for the different verifiers]
```

Timings for the Cameleer and Prusti programs were manually measured and are not automatically collected by this script; the numbers are included directly in the script so they may be printed alongside Heifer's timings.

As Cameleer and Prusti require rather different environments (Cameleer relies on the Why3 IDE, which requires a graphical environment, while Prusti was run using its OOPSLA 2021 artifact, which is a separate Docker image) and are less material to the claims about Heifer's functionality, we did not include them in our artifact.

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

## Claims supported by the artifact

- We claim that Heifer can verify all its examples listed in Table 1
- We claim that the verification timings of Heifer's examples are reproducible at least with respect to their order of magnitude; the exact timings vary depending on the underlying hardware, the versions of provers used and their internal heuristics, etc.

## Other Information on Heifer

### Build

The Dockerfile used to build the image is also available inside the image.
It shows all the system dependencies required to compile Heifer on top of an Ubuntu-based opam image.

```sh
docker build -t heifer-fm24 -f Dockerfile . --progress=plain
```

The OCaml dependencies required to build Heifer are listed with their versions in its `dune-project`.

### Project structure

The source code is in the `parsing` directory.
The project builds with dune, and the `dune` file in that directory contains a listing of the project's components.
A brief description of the relevant ones:

- hip: entry point
- ocamlfrontend: part of the OCaml 4.12 compiler frontend, modified to parse the `(*@ comments @*)` used for writing HSSL specifications
- hipcore: AST for staged/separation logic/pure formulae and operations such as pretty-printing, substitution, etc.
- hipprover: the entailment prover for staged formulae, which consists of modules for applying the forward rules, applying lemmas, proof search, biabduction-based normalization, and entailment checking
