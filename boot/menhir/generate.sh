#!/usr/bin/env bash

cp $(opam var lib)/menhirLib/menhirLib.ml* .

#	 Derived from promote-menhir in https://github.com/ocaml/ocaml/blob/trunk/Makefile.menhir
#	 Other useful options: --strict --explain --dump --log-grammar 1 --log-automaton 1 --require-aliases,
#	 --infer (but then --ocamlc needs to be supplied with all the right includes)
menhir --lalr --unused-token COMMENT --unused-token DOCSTRING --unused-token EOL --unused-token GREATERRBRACKET --fixed-exception --table --strategy simplified --base parser ../../lib/parsing/parser.mly
