open Syntax
open Bindlib

module OpInfo = struct
  let binary = function
    | Lt -> ("<", `Left, 4)
    | Le -> ("<=", `Left, 4)
    | Gt -> (">", `Left, 4)
    | Ge -> (">=", `Left, 4)
    | Eq -> ("=", `Left, 3)
    | Neq -> ("!=", `Left, 3)

  let unary = function Not -> ("!", 8) | Neg -> ("-", 8)

  (* Operator precedence is only comparable within a syntactic category *)
  let prec_prop_conj = 2
  let prec_hprop_pointsto = 5
  let prec_hprop_sepconj = 3
  let prec_staged_seq = 2
  let prec_staged_disj = 1
end

let parens_if cond pp ppf x = if cond then Fmt.pf ppf "(%a)" pp x else pp ppf x

(** Parenthesises minimally using precedence and associativity, following
    https://bernsteinbear.com/blog/precedence-printing/

    - Pass parent precedence down to children
    - If a child has lower precedence than the parent context, wrap in parens
    - If left associative, decrement for left child *)
let rec pp_term_prec prec ctxt ppf = function
  | TVar x -> Fmt.string ppf (name_of x)
  | TUnit -> Fmt.string ppf "()"
  | TTrue -> Fmt.string ppf "true"
  | TFalse -> Fmt.string ppf "false"
  | TInt i -> Fmt.int ppf i
  | TFun b ->
    let x, body, ctxt = unbind_in ctxt b in
    Fmt.pf ppf "@[<hov 2>fun %s ->@ %a@]" (name_of x)
      (pp_staged_spec_prec 0 ctxt)
      body
  | TTuple ts ->
    Fmt.pf ppf "@[<hov 2>(%a)@]"
      Fmt.(list ~sep:(any ",@ ") (pp_term_prec 0 ctxt))
      ts
  | TBinop (op, t1, t2) ->
    let sym, assoc, prec' = OpInfo.binary op in
    let left_prec = if assoc = `Right then prec' else prec' - 1 in
    let right_prec = if assoc = `Left then prec' else prec' - 1 in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a %s %a@]"
        (pp_term_prec left_prec ctxt)
        t1 sym
        (pp_term_prec right_prec ctxt)
        t2
    in
    parens_if (prec' <= prec) pp ppf ()
  | TUnop (op, t) ->
    let sym, prec' = OpInfo.unary op in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%s%a@]" sym (pp_term_prec (prec - 1) ctxt) t
    in
    parens_if (prec' <= prec) pp ppf ()

and pp_prop_prec prec ctxt ppf = function
  | PAtom t -> pp_term_prec 0 ctxt ppf t
  | PConj (t1, t2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a /\\@ %a@]"
        (pp_prop_prec (OpInfo.prec_prop_conj - 1) ctxt)
        t1
        (pp_prop_prec (OpInfo.prec_prop_conj - 1) ctxt)
        t2
    in
    parens_if (OpInfo.prec_prop_conj <= prec) pp ppf ()

and pp_hprop_prec prec ctxt ppf = function
  | HPure p -> pp_prop_prec 0 ctxt ppf p
  | HEmp -> Fmt.string ppf "emp"
  | HPointsTo (t1, t2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a ->@ %a@]" (pp_term_prec 0 ctxt) t1
        (pp_term_prec 0 ctxt) t2
    in
    parens_if (OpInfo.prec_hprop_pointsto <= prec) pp ppf ()
  | HSepConj (h1, h2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a *@ %a@]"
        (pp_hprop_prec (OpInfo.prec_hprop_sepconj - 1) ctxt)
        h1
        (pp_hprop_prec (OpInfo.prec_hprop_sepconj - 1) ctxt)
        h2
    in
    parens_if (OpInfo.prec_hprop_sepconj <= prec) pp ppf ()

and pp_staged_spec_prec prec ctxt ppf = function
  | Return t -> Fmt.pf ppf "@[<hov 2>ret@ %a@]" (pp_term_prec 0 ctxt) t
  | Requires h -> Fmt.pf ppf "@[<hov 2>req@ %a@]" (pp_hprop_prec 0 ctxt) h
  | Ensures h -> Fmt.pf ppf "@[<hov 2>ens@ %a@]" (pp_hprop_prec 0 ctxt) h
  | Sequence (s1, s2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 0>%a;@ %a@]"
        (pp_staged_spec_prec OpInfo.prec_staged_seq ctxt)
        s1
        (pp_staged_spec_prec (OpInfo.prec_staged_seq - 1) ctxt)
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
      Fmt.pf ppf "@[<hov 2>%a;@ %s.@ %a"
        (pp_staged_spec_prec 0 ctxt)
        s (name_of x)
        (pp_staged_spec_prec 0 ctxt)
        body
    in
    pp ppf ()
  | Apply (f, t) ->
    Fmt.pf ppf "@[<hov 2>%a@ %a@]" (pp_term_prec 0 ctxt) f (pp_term_prec 0 ctxt)
      t
  | Disjunct (s1, s2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 0>%a@ \\/@ %a@]"
        (pp_staged_spec_prec OpInfo.prec_staged_disj ctxt)
        s1
        (pp_staged_spec_prec OpInfo.prec_staged_disj ctxt)
        s2
    in
    parens_if (OpInfo.prec_staged_disj <= prec) pp ppf ()
  | Forall b ->
    let x, body, ctxt = unbind_in ctxt b in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>forall %s.@ %a@]" (name_of x)
        (pp_staged_spec_prec 0 ctxt)
        body
    in
    pp ppf ()
  | Exists b ->
    let x, body, ctxt = unbind_in ctxt b in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>exists %s.@ %a@]" (name_of x)
        (pp_staged_spec_prec 0 ctxt)
        body
    in
    pp ppf ()
  | Shift b ->
    let k, body, ctxt = unbind_in ctxt b in
    Fmt.pf ppf "@[<hov 2>shift %s.@ %a@]" (name_of k)
      (pp_staged_spec_prec 0 ctxt)
      body
  | Reset s ->
    Fmt.pf ppf "@[<hov 2>reset@ { %a }@]" (pp_staged_spec_prec 0 ctxt) s
  | Dollar (s, b) ->
    let k, body, ctxt = unbind_in ctxt b in
    let pp ppf () =
      Fmt.pf ppf "@[<v 0>@[<hov 2>$let %s =@ %a@] in@,%a@]" (name_of k)
        (pp_staged_spec_prec 0 ctxt)
        s
        (pp_staged_spec_prec 0 ctxt)
        body
    in
    pp ppf ()

let pp_staged_spec ppf s =
  pp_staged_spec_prec 0 (free_vars (box_staged_spec s)) ppf s

let pp_term ppf t = pp_term_prec 0 (free_vars (box_term t)) ppf t
let pp_prop ppf p = pp_prop_prec 0 (free_vars (box_prop p)) ppf p
let pp_hprop ppf h = pp_hprop_prec 0 (free_vars (box_hprop h)) ppf h
