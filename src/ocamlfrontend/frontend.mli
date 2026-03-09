open Core_lang

(** Parses and interprets a OCaml file (identified by name) as a verification unit *)
val parse_ocaml : string -> verification_unit
