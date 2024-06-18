(lang dune 3.6)
(using experimental_building_ocaml_compiler_with_dune 0.1)
(using coq 0.2)
(using directory-targets 0.1)
(using menhir 2.1)

(name heifer)
(generate_opam_files true)

(source
 (github songyahui/AlgebraicEffect))

(authors "Song Yahui, Darius Foo")

(maintainers "yahui_s@nus.edu.sg, darius.foo.tw@gmail.com")
(license MIT)

(package
 (name heifer)
 (synopsis "Verifier")
 (description "Verifier for imperative higher order programs")
 (depends
  (ocaml (>= 5))
  (z3 (= 4.12.2)) ; 4.12.4 has some unsat->unknown issues...
  (menhir (>= 20220210))
  (dune (>= 3.8.0))
  (ppx_deriving (>= 5.2.1))
  (ppx_expect (>= v0.15.1))
  (brr (>= 0.0.4))
  (why3-ide (>= 1.7.0))
  (js_of_ocaml (>= 5.4.0))
  (unionFind (>= 20220122))
  (visitors (>= 20210608))))
