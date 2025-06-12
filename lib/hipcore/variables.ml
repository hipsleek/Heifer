open Hiptypes

let res_var = Var "res"

let eq_res t = Atomic (EQ, res_var, t)

let is_eq_res = function
  | Atomic (op, t, _) -> op = EQ && t = res_var
  | _ -> false

let counter : int ref = ref 0

let reset_counter (i : int) : unit = counter := i

let fresh_variable (_ : 'a) : string =
  let i = !counter in
  counter := i + 1;
  "$v" ^ string_of_int i
