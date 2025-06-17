open Hiptypes
open Utils

let is_lambda_term = function
  | TLambda _ -> true
  | _ -> false
let emp = EmptyHeap
let seq = Lists.foldr1 (fun c t -> Sequence (c, t))
let req ?(p = True) ?(h = EmptyHeap) () = Require (p, h)
let ens ?(p = True) ?(h = EmptyHeap) () = NormalReturn (p, h)

(* these take tuples, unlike the data constructors *)
let req' (p,h) = Require (p, h)
let ens' (p, h) =  NormalReturn (p, h)

let bind v x y = Bind (v, x, y)
let disj = Lists.foldr1 (fun c t -> Disjunction (c, t))
let conj = Lists.foldr1 ~default:True (fun c t -> And (c, t))
let sep_conj = Lists.foldr1 ~default:EmptyHeap (fun c t -> SepConj (c, t))
let eq x y = Atomic (EQ, x, y)
let v x = Var x
let var v = Var v
let num n = Const (Num n)
let plus x y = BinOp (Plus, x, y)
let points_to x y = PointsTo (x, y)
let pts x y = PointsTo (x, y)

let rec conjuncts_of_pi (p : pi) : pi list =
  match p with
  | And (p1, p2) -> conjuncts_of_pi p1 @ conjuncts_of_pi p2
  | _ -> [p]

let rec conjuncts_of_kappa (k : kappa) : kappa list =
  match k with
  | EmptyHeap -> []
  | PointsTo _ -> [k]
  | SepConj (k1, k2) -> conjuncts_of_kappa k1 @ conjuncts_of_kappa k2
