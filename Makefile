export OCAMLRUNPARAM=b

all:
	dune build @doc-private
	dune build main/hip.exe
	# dune test -w
	# dune exec main/hip.exe src/sp_tests/0_heap_zero_once_twice.ml -w
