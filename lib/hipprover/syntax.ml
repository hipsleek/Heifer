open Hipcore
open Hiptypes
open Utils

let seq fs = Lists.foldr1 (fun c t -> Sequence (c, t)) fs
let req ?(p = True) ?(h = EmptyHeap) () = Require (p, h)
let ens ?(p = True) ?(h = EmptyHeap) () = NormalReturn (p, h)
let disj fs = Lists.foldr1 (fun c t -> Disjunction (c, t)) fs
let conj fs = Lists.foldr1 (fun c t -> And (c, t)) fs
let sep_conj fs = Lists.foldr1 (fun c t -> SepConj (c, t)) fs
let eq a b = Atomic (EQ, a, b)
let ( = ) = eq
let v x = Var x
let num n = Const (Num n)
let plus x y = BinOp (Plus, x, y)
