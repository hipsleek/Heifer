open Typedhip
open Syntax

let res_var ~typ = var "res" ~typ

let eq_res ?(typ = Any) t = eq (res_var ~typ) t

(** Given a pure formula of the form [res = t], return [Some t].
    Return [None] instead of it is not of this form. *)
let eq_res_term = function
  | Atomic (EQ, {term_desc = Var "res"; _}, t)
  | Atomic (EQ, t, {term_desc = Var "res"; _}) -> Some t
  | _ -> None

let is_eq_res t = eq_res_term t |> Option.is_some 

(* share these functions with the untyped module *)
let counter = Hipcore.Variables.counter

let reset_counter = Hipcore.Variables.reset_counter

let strip_trailing_digits = Hipcore.Variables.strip_trailing_digits

let fresh_variable = Hipcore.Variables.fresh_variable
