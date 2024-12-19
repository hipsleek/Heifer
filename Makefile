export OCAMLRUNPARAM=b

all:
	dune build @doc-private
	dune build main/hip.exe

.PHONY: test
test:
	dune test

.PHONY: test-all
test-all:
	TEST_ALL=1 dune test