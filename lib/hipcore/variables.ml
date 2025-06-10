open Hiptypes

let res_var = Var "res"

let counter : int ref = ref 0

let reset_counter (i : int) : unit = counter := i

let fresh_variable (_ : 'a) : string =
  let i = !counter in
  counter := i + 1;
  "$v" ^ string_of_int i
