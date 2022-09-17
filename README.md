# Algebraic Effect
Artifact evaluation for paper "Automated Temporal Verification for Algebraic Effects"


# About the Archive & Link to Research Paper  

This work is about temporal verification for Algebraic Effect and 
Effect handlers. 
The artifact takes programs with effects and handlers, written in Ocaml, 
and computes the execution traces of the effects without executing the 
program. 
Moreover, the programs are annotated with temporal specifications. 
The artifact also checks whether the real execution entails the 
provided specifications or not. 
Useful information are printed after our analysis, indicating unsatisfied 
post/pre-conditions. 





# Getting Started Guide 

## Docker 

```
docker pull yahuuuuui/aplas22ae
docker run -it yahuuuuui/aplas22ae:latest bash
cd home 
cd AlgebraicEffect 
eval $(opam env)
make
```

## Build from source (tested on Ubuntu 18)

- Dependencies:

Install opam: (cf. https://opam.ocaml.org/doc/Install.html)
```
sudo apt install git
sudo apt install curl
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
opam init
sudo apt install make 
sudo apt install gcc
```
Install ocaml and libraries:
```
opam switch create 4.13.1
eval $(opam env)
opam install menhir
```
Install z3 and dune:
```
opam init
eval `opam config env`
opam update
opam switch create 4.13.1
eval `opam config env`
opam install z3
sudo apt-get install whitedune
```
- Get the source code and build 
```
https://github.com/songyahui/AlgebraicEffect
cd AlgebraicEffect 
eval $(opam env)
make 
```

# Step-By-Step Instructions 


From the root directory:  
```
cd parsing 
```

There are 12 .ml files in `src/demo/` folder. 

The test files are for verifying
the coexistence of zero-shot, one-shot and multi-shot continuations, 
as we claimed in the introduction. 

```
 dune exec ./hip.exe ../src/demo/multi_shot0.ml
 dune exec ./hip.exe ../src/demo/multi_shot1.ml
 dune exec ./hip.exe ../src/demo/multi_shot2.ml
 dune exec ./hip.exe ../src/demo/multi_shot3.ml
 dune exec ./hip.exe ../src/demo/one_shot0.ml
 dune exec ./hip.exe ../src/demo/one_shot1.ml
 dune exec ./hip.exe ../src/demo/one_shot2.ml
 dune exec ./hip.exe ../src/demo/one_shot3.ml
```
In particular, the following two tests correspond to 
the example we show in Figure 10. 
```
 dune exec ./hip.exe ../src/demo/zero_shots0.ml
 dune exec ./hip.exe ../src/demo/zero_shots1.ml
```

This `loop0` test file corresponds to 
the example we show in Figure 1. 
```
 dune exec ./hip.exe ../src/demo/loop0.ml
```

All the verification results should pass. 


# Reproduce the evaluation data in Table 1 

From the root directory:  
```
cd parsing 
```

There are 12 .ml files in `src/evaluation/` folder, 
corresponding the 12 lines in Table 1. 

The main check points are the last 4 column: 
`#Prop(valid)`, 
`Avg-Prove(ms)`, 
`#Prop(invalid)`,
`and Avg-Dis(ms)`. 

For example, run 
```
dune exec ./hip.exe ../src/evaluation/test1.ml
```
will get the first line data at the last lines of the printing. 

Same for the rest lines. 


# What is inside the `root directory` ?

There are four main files/folders under the root directory:
- Makefile: a make file to make sure the parsing is working 
- README.md: instructions of get hands on the project
- parsing: the folder contains the source code
    1. "parsetree.ml": contains the AST structure 
    2. "parser.mly": implements the parser 
    3. "hip.ml": the main file of our forward verifier
    4. "sleek.ml": the main file of our back-end term rewriting system
    5. "Rewriting.ml": the implementation of the  term rewriting system
    6. "Pretty.ml": contains most of the pretty printing functions
- src: the folder contains the test cases
    1. "domo/": contains the examples in the paper
    2. "evaluation/": contains the test cases for the evaluation 
