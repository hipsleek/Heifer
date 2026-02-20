#/bin/bash

set -x
PREBUILD=$(mktemp -d)
mkdir $PREBUILD/heifer
BUILD=$PREBUILD/heifer

cp -r src test heifer.why dune-project $BUILD

# edit files
echo 'The project builds with OCaml 5.3.0.
Use `opam install --deps-only .` to install opam dependencies.
Use `dune build src test --display=short` to confirm that they are all installed. This should complete fast.
Then use `TEST_ALL=1 dune test --display=short` to run all the tests. This should take a few minutes.
If all goes well, nothing beyond the compilation commands should be printed.

The source code of the verifier is in src.
Benchmark programs are in test.
Handwritten proof scripts are in test/*.ml.
Files suffixed with _auto are use automation to search for proofs.
The outputs of running the tool in either mode are in test/*.t.' > $BUILD/readme.md

cd $PREBUILD
zip -r heifer.zip heifer

cd -
cp $PREBUILD/heifer.zip .