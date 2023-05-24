# Separation Logic for Unrestricted Effect Handlers

This work proposes a novel calculus based on Staged Separation Logic 
(SSL) to support unrestricted effect handlers, 
where zero/one/multi-shot continuations co-exist together with imperative effects.
SSL summaries behaviors in stages, 
explicitly revealing performed algebraic effects;
and allows modular descriptions/reasoning for  
effectful programs and their handlers. 
Our staged specification intuitively provides insights into unhandled effects 
and failed assertions. 
To show the feasibility, we prototype the automated verification system, 
prove its correctness, report 
on case studies, and present initial experimental results. 



# Working Examples:

All the example in 'src/evaluation' folder. 
In particular, 

- (example for exchange values ) 
dune exec ./hip.exe ../src/evaluation/11_exchange.ml

- (paper example multi-shot demonstration)
dune exec ./hip.exe ../src/evaluation/0_heap_zero_once_twice.ml
dune exec ./hip.exe ../src/evaluation/1_heap_zero_once_twice.ml
dune exec ./hip.exe ../src/evaluation/2_heap_zero_once_twice.ml


- (paper example multi-shot demonstration ==> weakened version)
dune exec ./hip.exe ../src/sp_tests/0a_heap_zero_once_twice.ml

- (paper example state monad examples) 
dune exec ./hip.exe ../src/sp_tests/2_memory_cell.ml   
dune exec ./hip.exe ../src/sp_tests/2a_memory_cell.ml
dune exec ./hip.exe ../src/sp_tests/2b_memory_cell_mix_handler.ml
dune exec ./hip.exe ../src/sp_tests/2c_memory_cell_mix_handler.ml

dune exec ./hip.exe ../src/sp_tests/3_memory_cell_nested.ml
dune exec ./hip.exe ../src/sp_tests/3a_memory_cell_nested.ml

dune exec ./hip.exe ../src/sp_tests/3b_memory_cell_nested.ml
has a bug

- paper example: two pointers 
15_two_pointers.ml 

- paper example: backtracking 
16_z_flip.ml 


# SYH old entailment (hiplib)

2, 10, for normalization 
8, 11 for entailment 

8, 11: different results due to weakest precondition. the preconditions inferred for the actual impl seem a bit too strong?
2: has req F. new entailment seems correct, should be false?
10, write_handler: is the spec right? there's no prior info about x1
10, read_handler: depends on write_handler, TBC

# What is inside the `root directory` ?

There are four main files/folders under the root directory:
- Makefile: a make file to make sure the parsing is working 
- README.md: instructions of get hands on the project
- parsing: the folder contains the source code
    1. "parsetree.ml": contains the AST structure 
    2. "parser.mly": implements the parser 
    3. "hip.ml": the main file of our forward verifier and entailment checking 
    6. "Pretty.ml": contains most of the pretty printing functions
- src: the folder contains the test cases
    2. "evaluation/": contains the test cases for the evaluation 





eval $(opam env)

cd parsing
dune exec ./hip.exe ../src/sp_tests/0_heap_zero_once_twice.ml


opam switch 4.14.0+flambda
dune exec ./hip.exe ../src/programs.t/parse_test.ml


TODO:
design the experiments to show that:
re-reasoning does not cause too much overhead. 
we can reason about multi-shot efficiently. 



======HIGH ORDER=======
1. dune exec ./hip.exe ../src/programs.t/test_ho.ml

2. dune exec ./hip.exe ../src/programs.t/test_new_entail.ml


TODO: write compose and applyN in 1 
verify the results in 2. 


info "FAIL, constr %s != %s@." c1 c2;
