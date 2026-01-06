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

  (* Operator precedence is only comparable within a syntactic category *)
  let unary = function Not -> ("!", 8) | Neg -> ("-", 8)
  let prop = function `Conj -> 2
  let hprop = function `PointsTo -> 5 | `SepConj -> 3
  let staged = function `Seq -> 2 | `Disj -> 1
end

let parens_if cond pp ppf x = if cond then Fmt.pf ppf "(%a)" pp x else pp ppf x

(** Parenthesises minimally using precedence and associativity, following
    https://bernsteinbear.com/blog/precedence-printing/

    - Pass parent precedence down to children
    - If a child has lower precedence than the parent context, wrap in parens
    - If left associative, decrement for left child *)
let rec pp_term_prec prec ppf = function
  | TVar x -> Fmt.string ppf (name_of x)
  | TUnit -> Fmt.string ppf "()"
  | TTrue -> Fmt.string ppf "true"
  | TFalse -> Fmt.string ppf "false"
  | TInt i -> Fmt.int ppf i
  | TFun b ->
    let x, body = unbind b in
    Fmt.pf ppf "@[<hov 2>fun %s ->@ %a@]" (name_of x) pp_staged_spec body
  | TTuple ts ->
    Fmt.pf ppf "@[<hov 2>(%a)@]" Fmt.(list ~sep:(any ",@ ") pp_term) ts
  | TBinop (op, t1, t2) ->
    let sym, assoc, prec' = OpInfo.binary op in
    let left_prec = if assoc = `Right then prec' else prec' - 1 in
    let right_prec = if assoc = `Left then prec' else prec' - 1 in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a %s %a@]" (pp_term_prec left_prec) t1 sym
        (pp_term_prec right_prec) t2
    in
    parens_if (prec' <= prec) pp ppf ()
  | TUnop (op, t) ->
    let sym, prec' = OpInfo.unary op in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%s%a@]" sym (pp_term_prec (prec - 1)) t
    in
    parens_if (prec' <= prec) pp ppf ()

and pp_term ppf t = pp_term_prec 0 ppf t

and pp_prop_prec prec ppf = function
  | PAtom t -> pp_term ppf t
  | PConj (t1, t2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a /\\@ %a@]"
        (pp_prop_prec (OpInfo.prop `Conj - 1))
        t1
        (pp_prop_prec (OpInfo.prop `Conj - 1))
        t2
    in
    parens_if (OpInfo.prop `Conj <= prec) pp ppf ()

and pp_prop ppf p = pp_prop_prec 0 ppf p

and pp_hprop_prec prec ppf = function
  | HPure p -> pp_prop ppf p
  | HEmp -> Fmt.string ppf "emp"
  | HPointsTo (t1, t2) ->
    let pp ppf () = Fmt.pf ppf "@[<hov 2>%a ->@ %a@]" pp_term t1 pp_term t2 in
    parens_if (OpInfo.hprop `PointsTo <= prec) pp ppf ()
  | HSepConj (h1, h2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a *@ %a@]"
        (pp_hprop_prec (OpInfo.hprop `SepConj - 1))
        h1
        (pp_hprop_prec (OpInfo.hprop `SepConj - 1))
        h2
    in
    parens_if (OpInfo.hprop `SepConj <= prec) pp ppf ()

and pp_hprop ppf h = pp_hprop_prec 0 ppf h

and pp_staged_spec_prec prec ppf = function
  | Return t -> Fmt.pf ppf "@[<hov 2>ret@ %a@]" pp_term t
  | Requires h -> Fmt.pf ppf "@[<hov 2>req@ %a@]" pp_hprop h
  | Ensures h -> Fmt.pf ppf "@[<hov 2>ens@ %a@]" pp_hprop h
  | Sequence (s1, s2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 0>%a;@ %a@]"
        (pp_staged_spec_prec (OpInfo.staged `Seq))
        s1
        (pp_staged_spec_prec (OpInfo.staged `Seq - 1))
        s2
    in
    parens_if (OpInfo.staged `Seq <= prec) pp ppf ()
  | Bind (s, b) ->
    let x, body = unbind b in
    (* let pp ppf () =
      Fmt.pf ppf "@[<v 0>@[<hov 2>let %s =@ %a@] in@,%a@]" (name_of x)
        pp_staged_spec s pp_staged_spec body
    in *)
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>%a;@ %s.@ %a" pp_staged_spec s (name_of x)
        pp_staged_spec body
    in
    pp ppf ()
  | Apply (f, t) -> Fmt.pf ppf "@[<hov 2>%a@ %a@]" pp_term f pp_term t
  | Disjunct (s1, s2) ->
    let pp ppf () =
      Fmt.pf ppf "@[<hov 0>%a@ \\/@ %a@]"
        (pp_staged_spec_prec (OpInfo.staged `Disj))
        s1
        (pp_staged_spec_prec (OpInfo.staged `Disj))
        s2
    in
    parens_if (OpInfo.staged `Disj <= prec) pp ppf ()
  | Forall b ->
    let x, body = unbind b in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>forall %s.@ %a@]" (name_of x) pp_staged_spec body
    in
    pp ppf ()
  | Exists b ->
    let x, body = unbind b in
    let pp ppf () =
      Fmt.pf ppf "@[<hov 2>exists %s.@ %a@]" (name_of x) pp_staged_spec body
    in
    pp ppf ()
  | Shift b ->
    let k, body = unbind b in
    Fmt.pf ppf "@[<hov 2>shift %s.@ %a@]" (name_of k) pp_staged_spec body
  | Reset s -> Fmt.pf ppf "@[<hov 2>reset@ { %a }@]" pp_staged_spec s
  | Dollar (s, b) ->
    let k, body = unbind b in
    let pp ppf () =
      Fmt.pf ppf "@[<v 0>@[<hov 2>$let %s =@ %a@] in@,%a@]" (name_of k)
        pp_staged_spec s pp_staged_spec body
    in
    pp ppf ()

and pp_staged_spec ppf s = pp_staged_spec_prec 0 ppf s

let string_of_term t = Fmt.str "%a" pp_term t
let string_of_prop p = Fmt.str "%a" pp_prop p
let string_of_hprop h = Fmt.str "%a" pp_hprop h
let string_of_staged_spec s = Fmt.str "%a" pp_staged_spec s
