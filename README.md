# AlgebraicEffect
effects system for continuation

# To run the parser 
cd parsing 

dune exec ./hip.exe ../src/programs/0_loop.ml



1) reverse = handler {print(s; k) 􏰀→ k (); print s}
2) perform takes one argument. 
3) context of infinite trace. 
4) debug dune exec parsing/hip.exe src/programs.t/fixpoint_infinite5.ml
5) debug high-order spec dune exec parsing/hip.exe src/programs.t/flip.ml

dune exec parsing/hip.exe src/programs.t/t0_foo_loop.ml

