open Syntax
open Bindlib

module OpInfo = struct
  let binary = function
    | Lt -> ("<", `Left, 8)
    | Le -> ("<=", `Left, 8)
    | Gt -> (">", `Left, 8)
    | Ge -> (">=", `Left, 8)
    | Eq -> ("=", `Left, 7)
    | Neq -> ("!=", `Left, 7)
    | Cons -> ("::", `Right, 9)
    | Plus -> ("+", `Right, 9)
    | Times -> ("*", `Right, 10)

  let unary = function Not -> ("!", 12) | Neg -> ("-", 12)
  let prec_prop_conj = 8
  let prec_prop_subsumes = 7
  let prec_prop_implies = 6
  let prec_hprop_pointsto = 5
  let prec_hprop_sepconj = 4
  let prec_staged_seq = 3
  let prec_staged_quantifier = 2
  let prec_staged_disj = 1
end

let parens_if cond pp ppf x = if cond then Fmt.pf ppf "(%a)" pp x else pp ppf x

(** Parenthesises minimally using precedence and associativity, following
    https://bernsteinbear.com/blog/precedence-printing/

    - Pass parent precedence down to children
    - If a child has lower precedence than the parent context, wrap in parens
    - If left associative, decrement for left child *)
let rec pp_term_prec prec ctxt ppf = function
  | Var x -> Fmt.string ppf (name_of x)
  | Symbol sym -> Fmt.string ppf sym.sym_name
  | Unit -> Fmt.string ppf "()"
  | Nil -> Fmt.string ppf "[]"
  | True -> Fmt.string ppf "true"
  | False -> Fmt.string ppf "false"
  | Int i -> Fmt.int ppf i
  (* | App (f, xs) ->
    Fmt.pf ppf "%s$(%a)" f Fmt.(list ~sep:(any ",@ ") (pp_term_prec 0 ctxt)) xs *)
  | Fun b ->
    let x, body, ctxt = unmbind_in ctxt b in
    Fmt.pf ppf "@[<hov 2>(fun %a ->@ %a)@]"
      Fmt.(array ~sep:(any " ") string)
      (names_of x) (pp_term_prec 0 ctxt) body
  | Tuple ts ->
    Fmt.pf ppf "@[<hov 2>(%a)@]"
      Fmt.(list ~sep:(any ",@ ") (pp_term_prec 0 ctxt))
      ts
  | Binop (op, t1, t2) ->
    let sym, assoc, prec' = OpInfo.binary op in
    let left_prec = if assoc = `Right then prec' else prec' - 1 in
    let right_prec = if assoc = `Left then prec' else prec' - 1 in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a%s%a@]"
        (pp_term_prec left_prec ctxt)
        t1 sym
        (pp_term_prec right_prec ctxt)
        t2
    in
    parens_if (prec' <= prec) pp ppf ()
  | Unop (op, t) ->
    let sym, prec' = OpInfo.unary op in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%s%a@]" sym (pp_term_prec (prec - 1) ctxt) t
    in
    parens_if (prec' <= prec) pp ppf ()
  (* | Forall b ->
    let x, body, ctxt = unmbind_in ctxt b in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>forall %a.@ %a"
        Fmt.(array ~sep:(any " ") string)
        (names_of x)
        (pp_term_prec (OpInfo.prec_prop_forall - 1) ctxt)
        body
    in
    pp ppf () *)
  | Implies (t1, t2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a =>@ %a@]"
        (pp_term_prec OpInfo.prec_prop_implies ctxt)
        t1
        (pp_term_prec (OpInfo.prec_prop_implies - 1) ctxt)
        t2
    in
    parens_if (OpInfo.prec_prop_conj <= prec) pp ppf ()
  | Conj (t1, t2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a /\\@ %a@]"
        (pp_term_prec (OpInfo.prec_prop_conj - 1) ctxt)
        t1
        (pp_term_prec OpInfo.prec_prop_conj ctxt)
        t2
    in
    parens_if (OpInfo.prec_prop_conj <= prec) pp ppf ()
  | Subsumes (t1, t2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a ⊑@ %a@]"
        (pp_term_prec (OpInfo.prec_prop_subsumes - 1) ctxt)
        t1
        (pp_term_prec (OpInfo.prec_prop_subsumes - 1) ctxt)
        t2
    in
    parens_if (OpInfo.prec_prop_subsumes <= prec) pp ppf ()
  | Emp -> Fmt.string ppf "emp"
  | PointsTo (t1, t2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a->%a@]" (pp_term_prec 0 ctxt) t1
        (pp_term_prec 0 ctxt) t2
    in
    parens_if (OpInfo.prec_hprop_pointsto <= prec) pp ppf ()
  | SepConj (h1, h2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a *@ %a@]"
        (pp_term_prec (OpInfo.prec_hprop_sepconj - 1) ctxt)
        h1
        (pp_term_prec (OpInfo.prec_hprop_sepconj - 1) ctxt)
        h2
    in
    parens_if (OpInfo.prec_hprop_sepconj <= prec) pp ppf ()
  | Requires h -> Fmt.pf ppf "req %a" (pp_term_prec 0 ctxt) h
  | Ensures h -> Fmt.pf ppf "ens %a" (pp_term_prec 0 ctxt) h
  | Sequence (s1, s2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 0>%a;@ %a@]"
        (pp_term_prec OpInfo.prec_staged_seq ctxt)
        s1
        (pp_term_prec (OpInfo.prec_staged_seq - 1) ctxt)
        s2
    in
    parens_if (OpInfo.prec_staged_seq <= prec) pp ppf ()
  | Bind (s, b) ->
    let x, body, ctxt = unbind_in ctxt b in
    (* let pp ppf () =
      Fmt.pf ppf "@[<v 0>@[<hov 2>let %s =@ %a@] in@,%a@]" (name_of x)
        (pp_staged_spec ctxt) s (pp_staged_spec ctxt) body
    in *)
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a;@ %s.@ %a@]"
        (pp_term_prec OpInfo.prec_staged_seq ctxt)
        s (name_of x)
        (pp_term_prec (OpInfo.prec_staged_seq - 1) ctxt)
        body
    in
    parens_if (OpInfo.prec_staged_seq <= prec) pp ppf ()
  | Apply (f, t) ->
    Fmt.pf ppf "@[<hov 2>%a@ %a@]" (pp_term_prec 0 ctxt) f
      Fmt.(list ~sep:(any "@ ") (pp_term_prec 0 ctxt))
      t
  | Disj (s1, s2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 0>%a@ \\/@ %a@]"
        (pp_term_prec (OpInfo.prec_staged_disj - 1) ctxt)
        s1
        (pp_term_prec OpInfo.prec_staged_disj ctxt)
        s2
    in
    parens_if (OpInfo.prec_staged_disj <= prec) pp ppf ()
  | Forall b ->
    let xs, body, ctxt = unmbind_in ctxt b in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>forall %a.@ %a@]"
        Fmt.(array ~sep:(any " ") string)
        (names_of xs)
        (pp_term_prec OpInfo.prec_staged_quantifier ctxt)
        body
    in
    parens_if (OpInfo.prec_staged_quantifier <= prec) pp ppf ()
  | Exists b ->
    let xs, body, ctxt = unmbind_in ctxt b in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>ex %a.@ %a@]"
        Fmt.(array ~sep:(any " ") string)
        (names_of xs)
        (pp_term_prec OpInfo.prec_staged_quantifier ctxt)
        body
    in
    parens_if (OpInfo.prec_staged_quantifier <= prec) pp ppf ()
  | Shift b ->
    let k, body, ctxt = unbind_in ctxt b in
    Fmt.pf ppf "@[<hov 2>shift %s.@ %a@]" (name_of k) (pp_term_prec 0 ctxt) body
  | Reset s -> Fmt.pf ppf "@[<hov 2>reset@ (%a)@]" (pp_term_prec 0 ctxt) s

let pp_term ppf s = pp_term_prec 0 (free_vars (box_staged_spec s)) ppf s
