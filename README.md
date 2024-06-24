# FM24 Artifact Evaluation

This README is meant to guide artifact evaluation for FM24 paper 28:
**Staged Specification Logic for Verifying Higher-Order Imperative Programs**.

## Abstract

Our artifact is a self-contained Docker image which contains the source code of Heifer, an automated verification tool based on the logic presented in Sections 2-5 of the paper, as well as the scripts and inputs required to run the experiments described in Section 6 of the paper.

## Running the artifact

After downloading the artifact from Zenodo, it may be run as follows.

```sh
# assuming current directory contains artifact,
# named heifer-fm24.tgz
docker load -i heifer-fm24.tgz
docker run -it --rm heifer-icfp24 bash
```

You should see the following before the shell prompt appears.

```
[Artifact of FM #28: Heifer]
To reproduce the paper's experiments, run benchmarks/ho/experiments.py
Further details may be found in README.md (vim and nano are pre-installed).
```

To check that everything is set up correctly:

```sh
# run a test
TEST=1 dune exec parsing/hip.exe src/examples/fold.ml
# should print "ALL OK!" if all is well
# remove TEST=1 to see output
```

## Structure of the artifact

All the source code of the artifact is in `/home/AlgebraicEffect`, the default directory after entering the shall.

The benchmarks mentioned in Section 6 and scripts to run them are in `/home/AlgebraicEffect/benchmarks/ho`.

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

- **Specification/Normed Spec**: the user-provided specification for this function, before and after normalization (Section 3.2)
- **Raw Post Spec/Normed Post**: the strongest postcondition of the function (Section 4), before and after normalization
- **Entail Check**: true iff the strongest postcondition entails the given specification (section 5)
- **Forward/Entail Time**: the time taken by each of these phases
- **Norm Time**: the time spent performing normalization, which may occur during both phases
- **Z3/Why3 Time**: the time spent in each of these provers, which may be called by both phases and by normalization
- **Overall Time**: the wall-clock time taken to verify this function

If a function does not have a user-provided specification, no verification takes place. In that case, the record for it will not contain an "Entail Check" entry.
The strongest postcondition is still computed and is used as the specification for subsequent calls to the function.

## Reproducing experiments

To reproduce the experiments in Section 6 of the paper, execute the following script.

```sh
benchmarks/ho/experiments.py
```

This runs Heifer on all 13 benchmark programs mentioned in Table 1.
The size of each program and the time taken to verify it is measured.
Finally, the aggregate sizes of all the programs for each verifier are printed.

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

## Correspondence with Table 1

For Heifer, each block corresponds to a row in Table 1.
The program sizes should match exactly, but the timings may not (see claims below).

Timings for the Cameleer and Prusti programs were manually measured and are not automatically collected by this script; the numbers are included directly in the script only so they may be printed alongside Heifer's timings.

As Cameleer and Prusti require rather different environments (Cameleer relies on the Why3 IDE, which requires a graphical environment, while Prusti was run using its OOPSLA 2021 artifact, which is a separate Docker image) and are less material to the claims about Heifer's functionality, we did not include them in our artifact.

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
