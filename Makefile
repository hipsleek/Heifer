
.PHONY: all
all:
	mkdir -p boot/menhir
	cp $(wildcard $(shell opam config var lib)/menhirLib/menhirLib.ml*) boot/menhir

#	 Derived from promote-menhir in https://github.com/ocaml/ocaml/blob/trunk/Makefile.menhir
#	 Other useful options: --strict --explain --dump --log-grammar 1 --log-automaton 1 --require-aliases,
#	 --infer (but then --ocamlc needs to be supplied with all the right includes)
	menhir --lalr --unused-token COMMENT --unused-token DOCSTRING --unused-token EOL --unused-token GREATERRBRACKET --fixed-exception --table --strategy simplified --base boot/menhir/parser parsing/parser.mly

	dune exec parsing/hip.exe src/programs/t0_foo.ml

.PHONY: test
test:
	dune exec src/programs/t0_foo.exe

.PHONY: testall
testall: src/programs/*.ml
	for file in $^; do \
		dune exec $${file/.ml/.exe}; \
	done
