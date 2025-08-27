type 'a formatter = Format.formatter -> 'a -> unit

(** Module type for representing the core recursive definitions of the AST. *)
module type AST = sig
  type binder
  type term
  type core_lang
  type pi
  type kappa
  type staged_spec

  type state = pi * kappa
end

(** Another module type for the AST, but with more types exposed,
    for functors that would need to use them. *)
module type ASTExtra = sig
  include AST

  type core_handler_ops
  type constr_case
  type pattern
  type tryCatchLemma
  type handler_type
  type instant
  type handling_cases
  type trycatch
end
