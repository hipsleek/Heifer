open Typedhip
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
let v ?(typ = TVar (Hipcore.Variables.fresh_variable ~v:"v" ())) x = {term_desc = Var x; term_type = typ}
let var = v
let num n = {term_desc = Const (Num n); term_type = Int}
let tnot t = {term_desc = TNot t; term_type = Bool}
let points_to x y = PointsTo (x, y)
let pts = points_to

let term term_desc term_type = {term_desc; term_type}

let binop op lhs rhs =
  let output_type =
    match op with
    | Plus | Minus | TTimes | TDiv | TPower -> Int
    | SConcat -> TyString
    | TCons -> lhs.term_type
    | TAnd | TOr -> Bool
  in
  term (BinOp (op, lhs, rhs)) output_type

let ctrue = term (Const TTrue) Bool
let lambda ?(id = "") params ?(spec = None) body =
  (* TODO fill in the actual type if possible using Arrow *)
  term (TLambda (id, params, spec, body)) Lamb

let rel op lhs rhs = term (Rel (op, lhs, rhs)) Bool

let plus = binop Plus
let tand = binop TAnd

let rec conjuncts_of_pi (p : pi) : pi list =
  match p with
  | And (p1, p2) -> conjuncts_of_pi p1 @ conjuncts_of_pi p2
  | _ -> [p]

let rec conjuncts_of_kappa (k : kappa) : kappa list =
  match k with
  | EmptyHeap -> []
  | PointsTo _ -> [k]
  | SepConj (k1, k2) -> conjuncts_of_kappa k1 @ conjuncts_of_kappa k2
