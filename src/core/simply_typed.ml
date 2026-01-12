open Syntax

let rec is_pure_term = function
  | Var _ -> true
  | Symbol _ -> true
  | Unit -> true
  | True -> true
  | False -> true
  | Int _ -> true
  | Fun _ -> true
  | Tuple _ -> true
  | Binop (_, t1, t2) -> is_pure_term t1 && is_pure_term t2
  | Unop (_, t) -> is_pure_term t
  | Nil -> true
  | Conj (t1, t2) -> is_pure_term t1 && is_pure_term t2
  | Disj (t1, t2) -> is_pure_term t1 && is_pure_term t2
  | Implies (t1, t2) -> is_pure_term t1 && is_pure_term t2
  | _ -> false
