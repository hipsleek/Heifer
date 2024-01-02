(lang dune 3.6)
(using experimental_building_ocaml_compiler_with_dune 0.1)
(using coq 0.2)
(using directory-targets 0.1)

(name hip)
(generate_opam_files true)

(source
 (github songyahui/AlgebraicEffect))

(authors "Song Yahui, Darius Foo")

(maintainers "e0210374@u.nus.edu, darius.foo.tw@gmail.com")
(license MIT)

(package
 (name hip)
 (synopsis "Verifier")
 (description "Verifier for imperative higher order programs")
 (depends
  (ocaml (>= 5))
  (z3 (>= 4.12.2))
  (menhir (>= 20220210))
  (dune (>= 3.8.0))
  (ppx_deriving (>= 5.2.1))
  (ppx_expect (>= v0.15.1))
  (brr (>= 0.0.4))
  (js_of_ocaml (>= 5.4.0))
  (unionFind (>= 20220122))
  (visitors (>= 20210608))))