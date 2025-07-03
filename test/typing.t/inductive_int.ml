
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

(* written strangely to test as-patterns *)
let rec pred n = match n with
  | Zero -> n
  | Succ (Succ _ as s) -> s
  | Succ (Zero as s) -> s

let id x =
  (*@ ens res=x @*)
  pred (Succ x)
  (* this doesn't work, since plus is only unfolded once *)
  (* and because currently the entailment checker doesn't have an equivalent for [subst]
     for pure equalities in the context *)
  (* pred (plus (Succ Zero) x) *)

