# AlgebraicEffect
Artifact evaluation for paper "Automated Temporal Verification for Algebraic Effects"

# To Test the code 


docker pull yahuuuuui/aplas22ae

docker run -it yahuuuuui/aplas22ae:latest bash

cd home 

cd AlgebraicEffect 

dune exec ./hip.exe ../src/demo/loop0.ml
