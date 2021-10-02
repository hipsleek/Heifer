
.PHONY: all
all:
	mkdir -p boot/menhir
	cp $(wildcard $(shell opam var lib)/menhirLib/menhirLib.ml*) boot/menhir

#	 Derived from promote-menhir in https://github.com/ocaml/ocaml/blob/trunk/Makefile.menhir
#	 Other useful options: --strict --explain --dump --log-grammar 1 --log-automaton 1 --require-aliases,
#	 --infer (but then --ocamlc needs to be supplied with all the right includes)
	menhir --lalr --unused-token COMMENT --unused-token DOCSTRING --unused-token EOL --unused-token GREATERRBRACKET --fixed-exception --table --strategy simplified --base boot/menhir/parser parsing/parser.mly

#	dune test
	OCAMLRUNPARAM=b dune exec parsing/hip.exe src/programs.t/flip.ml

# make test F=src/programs.t/t0_foo_loop.ml
.PHONY: test
test:
	opam exec --switch=4.12+domains+effects dune exec $(subst .ml,.exe,$(F))

.PHONY: testall
testall: src/programs.t/*.ml
	for file in $^; do \
		dune exec $${file/.ml/.exe}; \
	done
