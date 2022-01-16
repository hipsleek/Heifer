#!/usr/bin/env bash

set -x

coq_makefile -f _CoqProject -o Makefile
make
