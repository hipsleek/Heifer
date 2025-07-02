
type inductive_int = Zero | Succ of inductive_int

let rec plus n m = match n with
  | Zero -> m
  | Succ n -> Succ (plus n m)

let add_zero n 
(*@ ens res=n @*)
= plus Zero n

(* an induction hypothesis is automatically inferred so this passes *)
let add_zero_2 n
(*@ ens res=n @*)
= plus n Zero
