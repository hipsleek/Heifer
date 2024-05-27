
FROM ocaml/opam:ubuntu-23.04-ocaml-5.1

RUN git clone https://github.com/songyahui/AlgebraicEffect.git

WORKDIR AlgebraicEffect

RUN sudo apt-get update -y && \
  sudo apt-get install -y libgmp-dev pkg-config python3 libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev

RUN opam update && \
  opam install dune menhir ppx_deriving ppx_expect unionFind visitors z3 why3-ide

RUN eval $(opam env) && dune build @install
ENV PATH $PWD:$PATH