
FROM ocaml/opam:ubuntu-23.04-ocaml-5.1

USER root
WORKDIR /home

RUN git clone https://github.com/songyahui/AlgebraicEffect.git

WORKDIR AlgebraicEffect
RUN git checkout -t origin/fm24

RUN sudo apt-get update -y && \
  sudo apt-get install -y libgmp-dev pkg-config python3 python-is-python3 \
                          libcairo2-dev libexpat1-dev libgtk-3-dev libgtksourceview-3.0-dev \
                          vim nano

RUN opam update && \
  opam install --deps-only .

RUN eval $(opam env) && dune build @install
ENV PATH $PWD:$PATH

RUN ./benchmarks/ho/update_bashrc.sh