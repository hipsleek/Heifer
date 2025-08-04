open Typedhip
open Syntax

let res_var ~typ = var "res" ~typ

let eq_res ?(typ = Any) t = eq (res_var ~typ) t

let is_eq_res = function
  | Atomic (EQ, {term_desc = Var "res"; _}, _)
  | Atomic (EQ, _, {term_desc = Var "res"; _}) -> true
  | _ -> false

(* share these functions with the untyped module *)
let counter = Hipcore.Variables.counter

let reset_counter = Hipcore.Variables.reset_counter

let strip_trailing_digits = Hipcore.Variables.strip_trailing_digits

let fresh_variable = Hipcore.Variables.fresh_variable
