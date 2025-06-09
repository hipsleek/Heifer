open Hipcore
open Hiptypes

let seq fs = Utils.Lists.foldr1 (fun c t -> Sequence (c, t)) fs
let ens ?(p = True) ?(h = EmptyHeap) () = NormalReturn (p, h)
let conj fs = Utils.Lists.foldr1 (fun c t -> And (c, t)) fs
let sep_conj fs = Utils.Lists.foldr1 (fun c t -> SepConj (c, t)) fs
let eq a b = Atomic (EQ, a, b)
let ( = ) = eq
let v x = Var x
