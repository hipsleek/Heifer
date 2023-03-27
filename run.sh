#!/usr/bin/env bash

set -x

export OCAMLRUNPARAM=b

while true; do
  dune exec parsing/hip.exe src/programs.t/parse_test.ml -w
  sleep 1
done
