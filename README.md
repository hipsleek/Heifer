# Automated Verification for Multi-shot Continuations 



1. for primitive shared-memory concurrency
2. for memory manipulating nested handlers
3. connection with monadic. 
4. expressiveness between algebraic effects and reset/shift 


eval $(opam env)

cd parsing
dune exec ./hip.exe ../src/sp_tests/0_heap_zero_once_twice.ml


opam switch 4.14.0+flambda
dune exec ./hip.exe ../src/programs.t/parse_test.ml



working examples:

(paper figure 20)
dune exec ./hip.exe ../src/sp_tests/7b_exchange.ml

(paper figure 3)
dune exec ./hip.exe ../src/sp_tests/0_heap_zero_once_twice.ml


(paper figure 3, weakened version)
dune exec ./hip.exe ../src/sp_tests/0a_heap_zero_once_twice.ml