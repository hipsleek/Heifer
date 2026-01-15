export OCAMLRUNPARAM=b

.PHONY: all
all:
	@echo 'note: running unit tests only; use make test-all to run integration tests'
	dune build src @runtest --display=short

.PHONY: w
w:
	dune build src @runtest -w --display=short

.PHONY: test-all
test-all:
	TEST_ALL=1 dune test --display=short

# all: test
# 	# dune build @doc-private
# 	dune build main/hip.exe

.PHONY: test
test:
	@echo 'note: running unit tests only; use make test-all to run integration tests'
	dune test

debug-menhir:
	echo 'parse_term: TRUE' | menhir --dump --explain --interpret --interpret-show-cst --trace src/parse/parser.mly
# 	echo 'parse_staged_spec: LOWERCASE_IDENT LPAREN INT COMMA INT RPAREN EOF' | menhir --dump --explain --interpret --interpret-show-cst --trace src/parse/parser.mly