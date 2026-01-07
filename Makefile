export OCAMLRUNPARAM=b

all1:
	dune build src @runtest

w:
	dune build src @runtest -w

all: test
	# dune build @doc-private
	dune build main/hip.exe

.PHONY: test
test:
	@echo 'note: running unit tests only; use make test-all to run integration tests'
	dune test

.PHONY: test-all
test-all:
	TEST_ALL=1 dune test

debug-menhir:
	echo 'parse_staged_spec: EXISTS LOWERCASE_IDENT LOWERCASE_IDENT DOT ENSURES LOWERCASE_IDENT EQUAL LOWERCASE_IDENT SEMI LOWERCASE_IDENT DOT ENSURES LOWERCASE_IDENT EQUAL LOWERCASE_IDENT EOF' | menhir --dump --explain --interpret --interpret-show-cst --trace src/parse/parser.mly
# 	echo 'parse_staged_spec: LOWERCASE_IDENT LPAREN INT COMMA INT RPAREN EOF' | menhir --dump --explain --interpret --interpret-show-cst --trace src/parse/parser.mly