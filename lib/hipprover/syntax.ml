open Hipcore
open Hiptypes
open Utils

let emp = EmptyHeap
let seq = Lists.foldr1 (fun c t -> Sequence (c, t))
let req ?(p = True) ?(h = EmptyHeap) () = Require (p, h)
let ens ?(p = True) ?(h = EmptyHeap) () = NormalReturn (p, h)
let bind v x y = Bind (v, x, y)
let disj = Lists.foldr1 (fun c t -> Disjunction (c, t))
let conj = Lists.foldr1 ~default:True (fun c t -> And (c, t))
let sep_conj = Lists.foldr1 ~default:EmptyHeap (fun c t -> SepConj (c, t))
let eq x y = Atomic (EQ, x, y)
let v x = Var x
let var v = Var v
let num n = Const (Num n)
let plus x y = BinOp (Plus, x, y)
