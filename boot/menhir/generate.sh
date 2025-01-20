#!/usr/bin/env bash

cp $(opam var lib)/menhirLib/menhirLib.ml camlinternalMenhirLib.ml
cp $(opam var lib)/menhirLib/menhirLib.mli camlinternalMenhirLib.mli

#	 Derived from promote-menhir in https://github.com/ocaml/ocaml/blob/trunk/Makefile.menhir
#	 Other useful options: --strict --explain --dump --log-grammar 1 --log-automaton 1 --require-aliases,
#	 --infer (but then --ocamlc needs to be supplied with all the right includes)
menhir --lalr --unused-token COMMENT --unused-token DOCSTRING --unused-token EOL --unused-token GREATERRBRACKET --fixed-exception --table --strategy simplified --base parser ../../lib/parsing/parser.mly

# This comes from reset_shift, not sure whether it is necessary
cat parser.ml | sed 's/MenhirLib/CamlinternalMenhirLib/g' > parser1.ml
mv parser1.ml parser.ml
cat parser.mli | sed 's/MenhirLib/CamlinternalMenhirLib/g' > parser1.mli
mv parser1.mli parser.mli
