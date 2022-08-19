# Algebraic Effect
Artifact evaluation for paper "Automated Temporal Verification for Algebraic Effects"

# Installation 

## Docker 

```
docker pull yahuuuuui/aplas22ae
docker run -it yahuuuuui/aplas22ae:latest bash
cd home 
cd AlgebraicEffect 
eval $(opam env)
make
```

## Build from source 

- Dependencies:
```
opam switch create 4.13.1
eval $(opam env)
sudo apt-get install menhir
sudo apt-get install z3
```
- Get the source code and build 
```
git clone https://github.com/songyahui/EFFECTS.git
cd AlgebraicEffect 
eval $(opam env)
make 
```

# Test the functionality 


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