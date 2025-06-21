export OCAMLRUNPARAM=b

all: test
	dune build @doc-private
	dune build main/hip.exe

.PHONY: test
test:
	@echo 'note: running unit tests only; use make test-all to run integration tests'
	dune test

.PHONY: test-all
test-all:
	TEST_ALL=1 dune test