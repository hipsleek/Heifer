export OCAMLRUNPARAM=b

.PHONY: all
all:
	@echo 'note: running unit tests only'
	@echo 'use make test to run fast integration tests, and make test-all to run all tests'
	dune build src test @runtest

.PHONY: test
test:
	TEST=1 dune test

.PHONY: test-all
test-all:
	TEST_ALL=1 dune test

.PHONY: w
w:
	dune build src @runtest -w

debug-menhir:
	echo 'parse_term: TRUE' | menhir --dump --explain --interpret --interpret-show-cst --trace src/parse/parser.mly
# 	echo 'parse_staged_spec: LOWERCASE_IDENT LPAREN INT COMMA INT RPAREN EOF' | menhir --dump --explain --interpret --interpret-show-cst --trace src/parse/parser.mly