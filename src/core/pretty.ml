open Syntax
open Bindlib

(** {v
    ------------------------ high
P ::= true, false, unit, int, tuple, emp
    | P P
    | ... unop binop
    | x->1
    | P * P
    | P /\ P
    | req P | ens P
    | P; P | P; r. P
    | P \/ P
    | P <: P | P ==> P
    | sh k. P | λ x. P | forall x. P | exists x. P
    | < P > | ( P )
    ------------------------ low
    v} *)
module OpInfo = struct
  let binary = function
    | Lt -> ("<", `Left, 10)
    | Le -> ("<=", `Left, 10)
    | Gt -> (">", `Left, 10)
    | Ge -> (">=", `Left, 10)
    | Eq -> ("=", `Left, 9)
    | Neq -> ("!=", `Left, 9)
    | Cons -> ("::", `Right, 13)
    | Plus -> ("+", `Left, 11)
    | Minus -> ("-", `Left, 11)
    | Times -> ("*.", `Right, 12)

  let unary = function
    | Not -> ("!", 14)
    | Neg -> ("-", 14)

  let prec_app = 15
  let prec_pointsto = 8
  let prec_sepconj = 7
  let prec_conj = 6
  let prec_req_ens = 5
  let prec_seq = 4
  let prec_disj = 3
  let prec_entail = 2
  let prec_binder = 1
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
          (pp_term_prec OpInfo.prec_entail ctxt)
          t1
          (pp_term_prec (OpInfo.prec_entail - 1) ctxt)
          t2
      in
      parens_if (OpInfo.prec_conj <= prec) pp ppf ()
  | Conj (t1, t2) ->
      let pp ppf () =
        Fmt.pf ppf "@[<hov 2>%a /\\@ %a@]"
          (pp_term_prec (OpInfo.prec_conj - 1) ctxt)
          t1
          (pp_term_prec OpInfo.prec_conj ctxt)
          t2
      in
      parens_if (OpInfo.prec_conj <= prec) pp ppf ()
  | Subsumes (t1, t2) ->
      (* ⊑ *)
      let pp ppf () =
        Fmt.pf ppf "@[<hov 2>%a <:@ %a@]"
          (pp_term_prec OpInfo.prec_entail ctxt)
          t1
          (pp_term_prec (OpInfo.prec_entail - 1) ctxt)
          t2
      in
      parens_if (OpInfo.prec_entail <= prec) pp ppf ()
  | Emp -> Fmt.string ppf "emp"
  | PointsTo (t1, t2) ->
      let pp ppf () =
        Fmt.pf ppf "@[<hov 2>%a->%a@]" (pp_term_prec 0 ctxt) t1
          (pp_term_prec 0 ctxt) t2
      in
      parens_if (OpInfo.prec_pointsto <= prec) pp ppf ()
  | SepConj (h1, h2) ->
      let pp ppf () =
        Fmt.pf ppf "@[<hov 2>%a *@ %a@]"
          (pp_term_prec (OpInfo.prec_sepconj - 1) ctxt)
          h1
          (pp_term_prec (OpInfo.prec_sepconj - 1) ctxt)
          h2
      in
      parens_if (OpInfo.prec_sepconj <= prec) pp ppf ()
  | Requires h -> Fmt.pf ppf "req %a" (pp_term_prec OpInfo.prec_req_ens ctxt) h
  | Ensures h -> Fmt.pf ppf "ens %a" (pp_term_prec OpInfo.prec_req_ens ctxt) h
  | Sequence (s1, s2) ->
      let pp ppf () =
        Fmt.pf ppf "@[<hov 0>%a;@ %a@]"
          (pp_term_prec OpInfo.prec_seq ctxt)
          s1
          (pp_term_prec (OpInfo.prec_seq - 1) ctxt)
          s2
      in
      parens_if (OpInfo.prec_seq <= prec) pp ppf ()
  | Bind (s, b) ->
      let x, body, ctxt = unbind_in ctxt b in
      (* let pp ppf () =
      Fmt.pf ppf "@[<v 0>@[<hov 2>let %s =@ %a@] in@,%a@]" (name_of x)
        (pp_staged_spec ctxt) s (pp_staged_spec ctxt) body
    in *)
      let pp ppf () =
        Fmt.pf ppf "@[<hov 2>%a;@ %s.@ %a@]"
          (pp_term_prec OpInfo.prec_seq ctxt)
          s (name_of x)
          (pp_term_prec (OpInfo.prec_seq - 1) ctxt)
          body
      in
      parens_if (OpInfo.prec_seq <= prec) pp ppf ()
  | Apply (f, t) ->
      Fmt.pf ppf "@[<hov 2>%a@ %a@]"
        (pp_term_prec (OpInfo.prec_app - 1) ctxt)
        f
        Fmt.(list ~sep:(any "@ ") (pp_term_prec OpInfo.prec_app ctxt))
        t
  | Disj (s1, s2) ->
      let pp ppf () =
        Fmt.pf ppf "@[<hov 0>%a@ \\/ %a@]"
          (pp_term_prec (OpInfo.prec_disj - 1) ctxt)
          s1
          (pp_term_prec OpInfo.prec_disj ctxt)
          s2
      in
      parens_if (OpInfo.prec_disj <= prec) pp ppf ()
  | Forall b ->
      let xs, body, ctxt = unmbind_in ctxt b in
      let pp ppf () =
        Fmt.pf ppf "@[<hov 2>forall %a.@ %a@]"
          Fmt.(array ~sep:(any " ") string)
          (names_of xs)
          (pp_term_prec OpInfo.prec_binder ctxt)
          body
      in
      parens_if (OpInfo.prec_binder <= prec) pp ppf ()
  | Exists b ->
      let xs, body, ctxt = unmbind_in ctxt b in
      let pp ppf () =
        Fmt.pf ppf "@[<hov 2>ex %a.@ %a@]"
          Fmt.(array ~sep:(any " ") string)
          (names_of xs)
          (pp_term_prec OpInfo.prec_binder ctxt)
          body
      in
      parens_if (OpInfo.prec_binder <= prec) pp ppf ()
  | Shift b ->
      let k, body, ctxt = unbind_in ctxt b in
      Fmt.pf ppf "@[<hov 2>shift %s.@ %a@]" (name_of k) (pp_term_prec 0 ctxt)
        body
  | Reset s -> Fmt.pf ppf "@[<hov 2>reset@ (%a)@]" (pp_term_prec 0 ctxt) s

let pp_term ppf t = pp_term_prec 0 (free_vars (box_term t)) ppf t
