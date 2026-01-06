open Syntax
open Bindlib

let string_of_binop = function
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | Eq -> "="
  | Neq -> "!="

let string_of_unop = function
  | Not -> "!"
  | Neg -> "-"

let rec pp_term fmt = function
  | TVar x -> Format.fprintf fmt "%s" (name_of x)
  | TUnit -> Format.fprintf fmt "()"
  | TTrue -> Format.fprintf fmt "true"
  | TFalse -> Format.fprintf fmt "false"
  | TInt i -> Format.fprintf fmt "%d" i
  | TFun b ->
    let x, body = unbind b in
    Format.fprintf fmt "@[<hov 2>(fun %s ->@ %a)@]" (name_of x) pp_staged_spec body
  | TTuple ts ->
    Format.fprintf fmt "@[<hov 2>(%a)@]"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp_term) ts
  | TBinop (op, t1, t2) ->
    Format.fprintf fmt "@[<hov 2>(%a %s %a)@]" pp_term t1 (string_of_binop op) pp_term t2
  | TUnop (op, t) ->
    Format.fprintf fmt "@[<hov 2>(%s%a)@]" (string_of_unop op) pp_term t

and pp_prop fmt = function
  | PAtom t -> pp_term fmt t
  | PConj (t1, t2) ->
    Format.fprintf fmt "@[<hov 2>(%a /\\@ %a)@]" pp_prop t1 pp_prop t2

and pp_hprop fmt = function
  | HPure p -> pp_prop fmt p
  | HEmp -> Format.fprintf fmt "emp"
  | HPointsTo (t1, t2) ->
    Format.fprintf fmt "@[<hov 2>%a ->@ %a@]" pp_term t1 pp_term t2
  | HSepConj (h1, h2) ->
    Format.fprintf fmt "@[<hov 2>%a *@ %a@]" pp_hprop h1 pp_hprop h2

and pp_staged_spec fmt = function
  | Return t ->
    Format.fprintf fmt "@[<hov 2>return@ %a@]" pp_term t
  | Requires h ->
    Format.fprintf fmt "@[<hov 2>req@ %a@]" pp_hprop h
  | Ensures h ->
    Format.fprintf fmt "@[<hov 2>ens@ %a@]" pp_hprop h
  | Sequence (s1, s2) ->
    Format.fprintf fmt "@[<v 0>%a;@,%a@]" pp_staged_spec s1 pp_staged_spec s2
  | Bind (s, b) ->
    let x, body = unbind b in
    Format.fprintf fmt "@[<v 0>@[<hov 2>let %s =@ %a@] in@,%a@]"
      (name_of x) pp_staged_spec s pp_staged_spec body
  | Apply (f, t) ->
    Format.fprintf fmt "@[<hov 2>%a@ %a@]" pp_term f pp_term t
  | Disjunct (s1, s2) ->
    Format.fprintf fmt "@[<v 0>@[<hov 2>(%a)@]@ \\/@ @[<hov 2>(%a)@]@]"
      pp_staged_spec s1 pp_staged_spec s2
  | Forall b ->
    let x, body = unbind b in
    Format.fprintf fmt "@[<hov 2>forall %s.@ %a@]" (name_of x) pp_staged_spec body
  | Exists b ->
    let x, body = unbind b in
    Format.fprintf fmt "@[<hov 2>exists %s.@ %a@]" (name_of x) pp_staged_spec body
  | Shift b ->
    let k, body = unbind b in
    Format.fprintf fmt "@[<hov 2>shift %s.@ %a@]" (name_of k) pp_staged_spec body
  | Reset s ->
    Format.fprintf fmt "@[<hov 2>reset@ { %a }@]" pp_staged_spec s
  | Dollar (s, b) ->
    let k, body = unbind b in
    Format.fprintf fmt "@[<v 0>@[<hov 2>$let %s =@ %a@] in@,%a@]"
      (name_of k) pp_staged_spec s pp_staged_spec body
