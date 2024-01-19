
(* https://rosettacode.org/wiki/Accumulator_factory *)

let accumulator init =
  let total = ref init in
  let acc x
  (*@ ex t; req total->t; ens total->t+x @*)
  = total := !total + x; !total in
  acc

external sum : int -> int -> int -> int = "accumulator_factory.Extras.sum"

let sum_aux x n init =
  let total = ref init in
  let rec aux x n =
    if n = 0 then !total
    else let _ = total := !total + x in aux x (n - 1)
  in
  aux n

let test init x n
(*@ ex r; sum_aux(x,n,init,r); ens res=r @*)
= let acc = accumulator init in
  let rec repeat x n =
    if n = 0 then (acc 0)
    else let r = acc x in repeat x (n - 1)
  in
  repeat x n
