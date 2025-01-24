let rec list_identity_aux lst =
  match lst with
  | [] -> shift k k
  | x :: xs -> x :: list_identity_aux xs

(* this cannot be proven atm *)
let list_identity lst
(*@ ens res = lst @*)
= (reset (list_identity_aux lst)) []

let empty_list ()
(*@ ens res = [] @*)
= (reset (list_identity_aux [])) []

(* this cannot be proven atm *)
let singleton_list ()
(*@ ens res = [1] @*)
= (reset (list_identity_aux [1])) []
