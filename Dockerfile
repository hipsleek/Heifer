
FROM ocaml/opam:ubuntu-23.04-ocaml-5.1

RUN opam update

RUN git clone https://github.com/songyahui/AlgebraicEffect.git

WORKDIR AlgebraicEffect
RUN git checkout -t origin/fm24

RUN sudo apt-get update -y && sudo apt-get install -y libgmp-dev pkg-config python3

RUN opam install dune menhir ppx_deriving ppx_expect unionFind visitors z3

RUN sudo apt-get install -y libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev
RUN opam install why3-ide

RUN eval $(opam env) && dune build @install
ENV PATH $PWD:$PATH

RUN sudo apt-get install -y vim nano
RUN sudo apt-get install -y python3 python-is-python3

RUN ./benchmarks/ho/update_bashrc.sh