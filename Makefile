
export OCAMLRUNPARAM=b 

all:
	dune build parsing/hip.exe
#	dune build parsing/hip.exe -w
#	dune test -w
#	dune exec parsing/hip.exe src/sp_tests/0_heap_zero_once_twice.ml -w
