
(* https://rosettacode.org/wiki/Accumulator_factory *)

let accumulator init =
  let total = ref init in
  fun n ->
    total := !total + n;
    !total

let test n
(*@ ens res=n @*)
= let acc = accumulator 0 in
  let rec repeat x n =
    if n = 0 then (acc 0)
    else acc x; repeat x (n - 1)
  in
  repeat 1 n
