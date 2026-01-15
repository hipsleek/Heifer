
```ocaml
open Heifer.Interactive
```

First, a definition of `foldr`.

```ocaml
declare {|foldr f init xs =
  ens xs=[]; init
  \/ ex h t. ens xs=h::t; foldr f init t; r. f h r|}
```


```ocaml
# start_proof "forall xs. foldr (fun c t -> c + t) 0 xs <: sum xs";

----------------------------------------
forall xs. foldr (fun c t -> c+t) 0 xs <: sum xs

- : unit = ()

# forall_intro ()
xs
----------------------------------------
   foldr (fun c t -> c+t) 0 xs
<: sum xs

- : unit = ()
```

We proceed by induction on the structure of the list `xs`.

```ocaml
# induction ~name:"IH" `List "xs"
xs
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   foldr (fun c t -> c+t) 0 xs
<: sum xs

- : unit = ()

# unfold "foldr"
xs
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   ens xs=[]; 0 \/
   (ex h t.
      ens xs=h::t; foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r)
<: sum xs

- : unit = ()

# disj_elim ()
xs
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   ens xs=[]; 0
<: sum xs
(1 more goals)

- : unit = ()
```

Base case

```ocaml
# intro_pure "H"
xs
H: xs=[]
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   0
<: sum xs
(1 more goals)

- : unit = ()

# prove ()
module M
  use heifer.Heifer

  goal goal1: forall xs : term. (xs = TNil) -> ((TInt 0) = (xs.sum))
end
==> Valid


xs
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   ex h t.
     ens xs=h::t; foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
<: sum xs

- : unit = ()
```

Inductive case

```ocaml
# exists_elim ()
h, t, xs
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   ens xs=h::t; foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
<: sum xs

- : unit = ()

# intro_pure "Hxs"
h, t, xs
Hxs: xs=h::t
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   foldr (fun c t1 -> c+t1) 0 t; r. (fun c t1 -> c+t1) h r
<: sum xs

- : unit = ()
```

To use the induction hypothesis, we have to prove that `t` is a sublist of `xs`.
This lets us rewrite the call to `foldr`.

```ocaml
# rewrite "IH"
h, t, xs
Hxs: xs=h::t
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
sublist t xs
(1 more goals)

- : unit = ()

# prove ()
module M
  use heifer.Heifer

  goal goal1:
    forall h : term, t : term, xs : term.
      (xs = (TCons h t)) -> (sublist t xs)
end
==> Valid


h, t, xs
Hxs: xs=h::t
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   sum t; r. (fun c t1 -> c+t1) h r
<: sum xs

- : unit = ()
```

Having done that, the goal follows from the definition of `sum`.

```ocaml
# simpl ()
h, t, xs
Hxs: xs=h::t
IH: forall xs1. sublist xs1 xs => foldr (fun c t -> c+t) 0 xs1 <: sum xs1
----------------------------------------
   sum t; r. h+r
<: sum xs

- : unit = ()

# prove ()
module M
  use heifer.Heifer

  goal goal1:
    forall h : term, t : term, xs : term.
      (xs = (TCons h t)) -> ((plus h (t.sum)) = (xs.sum))
end
==> Valid

no more goals
- : unit = ()
```
