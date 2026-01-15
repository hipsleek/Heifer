(* 

(* original program *)

let accumulator init =
  let total = ref init in
  let acc x
  (*@ ex t; req total->t; ens total->t+x/\res=t+x @*)
  = total := !total + x; !total in
  acc

let test x n init (* FIXME *)
(*@ req n>=0; ens res=init+(n*.x) @*)
= let acc = accumulator init in
  let rec repeat x k
  = if k = 0 then acc 0
    else (acc x; repeat x (k - 1))
  in
  repeat x n

(* modified, in development *)

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
  repeat x n *)


(* https://rosettacode.org/wiki/Accumulator_factory *)

let accumulator init
(*@ ex total; ens total->init/\res=(fun x r (*@ ex t; req total->t; ens total->t+x/\r=t+x @*)) @*)
= let total = ref init in
  let acc x
  (*@ ex t; req total->t; ens total->t+x/\res=t+x @*)
  = total := !total + x; !total
  in
  acc

let test x n init (* FIXME *)
(* req n>=0; ens res=init+(n*.x) @*)
= let acc = accumulator init in
  let rec repeat x k
  (*@ ens k<=0; ex i; req total->i; ens total->i/\res=i
    \/ ens k>0; ex i; req total->i; ens total->i+x; repeat(x, k-1, res)
  @*)
  = if k <= 0 then acc 0
    else (acc x; repeat x (k - 1))
  in
  (* req n>=0; ens res=init+(n*.x) @*)
  (* let intermediate x n
    (* ens k<=0; ex total i; req total->i; ens total->i/\res=i
    \/ ens k>0; ex total i; req total->i; ens total->i+x; repeat(x, k-1, res)
    @*)
    = repeat x n
  in
  intermediate x n *)
  repeat x n

(* let use x n init
(* req n>=0; ens res=init+(n*.x) @*)
= test x n init *)
