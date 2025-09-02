(lang dune 3.17)
(using experimental_building_ocaml_compiler_with_dune 0.1)
(using coq 0.2)
(using directory-targets 0.1)
(using menhir 2.1)

(name heifer)
(generate_opam_files true)

(source
 (github hipsleek/Heifer))

(authors "Song Yahui, Darius Foo")

(maintainers "yahui_s@nus.edu.sg, darius.foo.tw@gmail.com")
(license MIT)

(package
 (name heifer)
 (synopsis "Program verifier")
 (description "A verifier for effectful, higher-order OCaml programs")
 (depends
  (ocaml (>= 5))
  (z3 (>= 4.12.2))
  (menhir (>= 20220210))
  (iter (>= 1.9))
  (dune (>= 3.8.0))
  (ppx_deriving (>= 5.2.1))
  (ppx_expect (>= v0.15.1))
  (brr (>= 0.0.4))
  (why3-ide (>= 1.8.0))
  (js_of_ocaml (>= 5.4.0))
  (unionFind (>= 20220122))
  (visitors (>= 20210608))
  (pprint (>= 20230830))))
