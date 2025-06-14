open Hiptypes

let res_var = Var "res"

let eq_res t = Atomic (EQ, res_var, t)

let is_eq_res = function
  | Atomic (op, t, _) -> op = EQ && t = res_var
  | _ -> false

let counter : int ref = ref 0

let reset_counter (i : int) : unit = counter := i

let strip_trailing_digits = Str.global_replace (Str.regexp "[0-9]*$") ""

let fresh_variable ?v _ : string =
  let i = !counter in
  counter := i + 1;
  match v with
  | None -> Format.asprintf "v%d" i
  | Some v -> Format.asprintf "%s%d" (strip_trailing_digits v) i
