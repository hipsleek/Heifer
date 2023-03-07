all:
	OCAMLRUNPARAM=b dune test -w
	OCAMLRUNPARAM=b dune exec parsing/hip.exe src/sp_tests/0_heap_zero_once_twice.ml -w
