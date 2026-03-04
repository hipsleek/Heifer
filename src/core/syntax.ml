open Bindlib
open Util

type metavar = { mv_name : string }

(** User-defined symbol (top-level declaration). *)
type symbol = { sym_name : string }

type binop =
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Neq
  | Plus
  | Minus
  | Times
  | Cons

type unop =
  | Not
  | Neg

(** Atomic term: variables, (literal) constants, functions, primitives; propositions; heap
    propositions; and staged specification formulae. *)
type term =
  | Var of term var
  | Symbol of symbol
  | Unit
  | True
  | False
  | Int of int
  | Fun of (term, term) mbinder
  | Apply of term * term list
  | Tuple of term list
  | Binop of binop * term * term
  | Unop of unop * term
  | Nil
  | ONone
  | OSome of term
  | Conj of term * term
  | Disj of term * term
  | Implies of term * term
  | Subsumes of term * term
  | Emp
  | PointsTo of term * term
  | SepConj of term * term
  | Wand of term * term
  | Requires of term
  | Ensures of term
  | Sequence of term * term
  | Bind of term * (term, term) binder
  | Forall of (term, term) mbinder
  | Exists of (term, term) mbinder
  | Shift of (term, term) binder
  | Reset of term
(* | Dollar of term * (term, term) binder *)

type def = (term, term) mbinder

(** Top level declaration.

    [Dfun] declares a possibly recursive function. *)
type decl = Dfun of symbol * def

module Tm = struct
  let var x = Var x
  let symbol sym = Symbol sym
  let unit = Unit
  let nil = Nil
  let true_ = True
  let false_ = False
  let int i = Int i
  let tuple ts = Tuple ts
  let fun_ b = Fun b
  let apply t ts = Apply (t, ts)
  let binop op t1 t2 = Binop (op, t1, t2)
  let unop op t = Unop (op, t)
  let none = ONone
  let some t = OSome t
  let conj t1 t2 = Conj (t1, t2)
  let disj t1 t2 = Disj (t1, t2)
  let implies t1 t2 = Implies (t1, t2)
  let subsumes t1 t2 = Subsumes (t1, t2)
  let emp = Emp
  let pointsto t1 t2 = PointsTo (t1, t2)
  let sepconj t1 t2 = SepConj (t1, t2)
  let wand t1 t2 = Wand (t1, t2)
  let requires t = Requires t
  let ensures t = Ensures t
  let sequence t1 t2 = Sequence (t1, t2)
  let bind t1 t2 = Bind (t1, t2)
  let forall b = Forall b
  let exists b = Exists b
  let shift b = Shift b
  let reset t = Reset t
end

(** Smart constructors that wrap data in [Bindlib.box]. *)
module Mk = struct
  let var = box_var
  let symbol sym = box (Symbol sym)
  let unit = box Unit
  let nil = box Nil
  let none = box ONone
  let some = box_apply (fun t -> OSome t)
  let true_ = box True
  let false_ = box False
  let int i = box (Int i)
  let tuple = box_apply Tm.tuple
  let fun_ = box_apply Tm.fun_
  let apply = box_apply2 Tm.apply
  let binop op = box_apply2 (Tm.binop op)
  let unop op = box_apply (Tm.unop op)
  let conj = box_apply2 Tm.conj
  let disj = box_apply2 Tm.disj
  let implies = box_apply2 Tm.implies
  let subsumes = box_apply2 Tm.subsumes
  let emp = box Emp
  let pointsto = box_apply2 Tm.pointsto
  let sepconj = box_apply2 Tm.sepconj
  let wand = box_apply2 Tm.wand
  let requires = box_apply Tm.requires
  let ensures = box_apply Tm.ensures
  let sequence = box_apply2 Tm.sequence
  let bind = box_apply2 Tm.bind
  let forall = box_apply Tm.forall
  let exists = box_apply Tm.exists
  let shift = box_apply Tm.shift
  let reset = box_apply Tm.reset
end

module Constr = struct
  let sepconj = function
    | [] -> Emp
    | ts -> Lists.fold_right1 Tm.sepconj ts

  let conj = function
    | [] -> True
    | ts -> Lists.fold_right1 Tm.conj ts

  let sequence = function
    | [] -> invalid_arg "sequence: empty list"
    | ts -> Lists.fold_right1 Tm.sequence ts

  let eq t1 t2 = Binop (Eq, t1, t2)
end

let new_tvar = new_var (fun v -> Var v)

let rec box_term = function
  | Var x -> Mk.var x
  | Symbol sym -> Mk.symbol sym
  | Unit -> Mk.unit
  | Nil -> Mk.nil
  | ONone -> Mk.none
  | OSome t -> Mk.some (box_term t)
  | True -> Mk.true_
  | False -> Mk.false_
  | Apply (t, ts) -> Mk.apply (box_term t) (box_term_list ts)
  | Int i -> Mk.int i
  | Tuple ts -> Mk.tuple (box_term_list ts)
  | Fun b -> Mk.fun_ (box_term_mbinder b)
  | Binop (op, t1, t2) -> Mk.binop op (box_term t1) (box_term t2)
  | Unop (op, t) -> Mk.unop op (box_term t)
  | Conj (t1, t2) -> Mk.conj (box_term t1) (box_term t2)
  | Disj (t1, t2) -> Mk.disj (box_term t1) (box_term t2)
  | Implies (t1, t2) -> Mk.implies (box_term t1) (box_term t2)
  | Subsumes (t1, t2) -> Mk.subsumes (box_term t1) (box_term t2)
  | Emp -> Mk.emp
  | PointsTo (t1, t2) -> Mk.pointsto (box_term t1) (box_term t2)
  | SepConj (t1, t2) -> Mk.sepconj (box_term t1) (box_term t2)
  | Wand (t1, t2) -> Mk.wand (box_term t1) (box_term t2)
  | Requires p -> Mk.requires (box_term p)
  | Ensures p -> Mk.ensures (box_term p)
  | Sequence (t1, s2) -> Mk.sequence (box_term t1) (box_term s2)
  | Bind (s, b) -> Mk.bind (box_term s) (box_term_binder b)
  | Forall b -> Mk.forall (box_term_mbinder b)
  | Exists b -> Mk.exists (box_term_mbinder b)
  | Shift b -> Mk.shift (box_term_binder b)
  | Reset s -> Mk.reset (box_term s)

and box_term_binder b = box_binder box_term b
and box_term_mbinder b = box_mbinder box_term b
and box_term_list ts = box_list (List.map box_term ts)

type prop = term
type hprop = term
type staged_spec = term

type sort =
  | Sort_term
  | Sort_prop
  | Sort_hprop
  | Sort_staged_spec

let pp_sort ppf = function
  | Sort_term -> Format.fprintf ppf "Sort_term"
  | Sort_prop -> Format.fprintf ppf "Sort_prop"
  | Sort_hprop -> Format.fprintf ppf "Sort_hprop"
  | Sort_staged_spec -> Format.fprintf ppf "Sort_staged_spec"

module Sort = struct
  exception Invalid_sort of string
  exception Sort_mismatch of string

  let invalid_sort msg = raise (Invalid_sort msg)
  let sort_mismatch msg = raise (Sort_mismatch msg)
end

module TV = struct
  type t = term var

  let compare = compare_vars
end

(** Set and map of term variables. *)
module TVSet = Set.Make (TV)

module TVSets = struct
  let add_array arr = Array.fold_right TVSet.add arr
  let of_array arr = add_array arr TVSet.empty
end

module TVMap = Map.Make (TV)

module Sym = struct
  type t = symbol

  let compare sym1 sym2 = String.compare sym1.sym_name sym2.sym_name
end

(** Set and map of symbols. *)
module SymSet = Set.Make (Sym)

module SymMap = Map.Make (Sym)

let rec equal_term t1 t2 =
  match (t1, t2) with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Symbol t1, Symbol s2 -> t1 = s2
  | Unit, Unit -> true
  | True, True -> true
  | False, False -> true
  | Int i1, Int i2 -> i1 = i2
  | Fun b1, Fun b2 -> eq_mbinder equal_term b1 b2
  | Apply (t1, ts1), Apply (t2, ts2) -> equal_term t1 t2 && equal_term_list ts1 ts2
  | Tuple ts1, Tuple ts2 -> equal_term_list ts1 ts2
  | Binop (op1, t11, t12), Binop (op2, t21, t22) ->
      op1 = op2 && equal_term t11 t21 && equal_term t12 t22
  | Unop (op1, t1), Unop (op2, t2) -> op1 = op2 && equal_term t1 t2
  | Nil, Nil -> true
  | ONone, ONone -> true
  | OSome t1, OSome t2 -> equal_term t1 t2
  | Conj (t11, t12), Conj (t21, t22) -> equal_term t11 t21 && equal_term t12 t22
  | Disj (t11, t12), Disj (t21, t22) -> equal_term t11 t21 && equal_term t12 t22
  | Implies (t11, t12), Implies (t21, t22) -> equal_term t11 t21 && equal_term t12 t22
  | Subsumes (s11, s12), Subsumes (s21, s22) -> equal_term s11 s21 && equal_term s12 s22
  | Emp, Emp -> true
  | PointsTo (t11, t12), PointsTo (t21, t22) -> equal_term t11 t21 && equal_term t12 t22
  | SepConj (t11, t12), SepConj (t21, t22) -> equal_term t11 t21 && equal_term t12 t22
  | Wand (t11, t12), Wand (t21, t22) -> equal_term t11 t21 && equal_term t12 t22
  | Requires t1, Requires t2 -> equal_term t1 t2
  | Ensures t1, Ensures t2 -> equal_term t1 t2
  | Sequence (t11, t12), Sequence (t21, t22) -> equal_term t11 t21 && equal_term t12 t22
  | Bind (t1, b1), Bind (t2, b2) -> equal_term t1 t2 && eq_binder equal_term b1 b2
  | Forall b1, Forall b2 -> eq_mbinder equal_term b1 b2
  | Exists b1, Exists b2 -> eq_mbinder equal_term b1 b2
  | Shift b1, Shift b2 -> equal_term_binder b1 b2
  | Reset t1, Reset s2 -> equal_term t1 s2
  | _, _ -> false

and equal_term_binder b1 b2 = eq_binder equal_term b1 b2
and equal_term_mbinder b1 b2 = eq_mbinder equal_term b1 b2

and equal_term_list ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> true
  | t1 :: ts1, t2 :: ts2 -> equal_term t1 t2 && equal_term_list ts1 ts2
  | _, _ -> false

let rec dump_term ppf t =
  match t with
  | Sequence (a, b) -> Fmt.pf ppf "@[<hov 2>Sequence (%a,@ %a)@]" dump_term a dump_term b
  | Var x -> Fmt.pf ppf "@[<hov 2>Var %s@]" (Bindlib.name_of x)
  | Symbol s -> Fmt.pf ppf "@[<hov 2>Symbol %s@]" s.sym_name
  | Unit -> Fmt.string ppf "Unit"
  | True -> Fmt.string ppf "True"
  | False -> Fmt.string ppf "False"
  | Int i -> Fmt.pf ppf "@[<hov 2>Int %d@]" i
  | Fun b ->
      let xs, body = Bindlib.unmbind b in
      let args = String.concat " " (Array.to_list (Array.map Bindlib.name_of xs)) in
      Fmt.pf ppf "@[<hov 2>Fun (%s.@ %a)@]" args dump_term body
  | Tuple ts -> Fmt.pf ppf "@[<hov 2>Tuple [%a]@]" (Fmt.list ~sep:Fmt.comma dump_term) ts
  | Binop (op, t1, t2) ->
      let op_s =
        match op with
        | Lt -> "Lt"
        | Le -> "Le"
        | Gt -> "Gt"
        | Ge -> "Ge"
        | Eq -> "Eq"
        | Neq -> "Neq"
        | Plus -> "Plus"
        | Minus -> "Minus"
        | Times -> "Times"
        | Cons -> "Cons"
      in
      Fmt.pf ppf "@[<hov 2>Binop (%s,@ %a,@ %a)@]" op_s dump_term t1 dump_term t2
  | Unop (op, t) ->
      let op_s =
        match op with
        | Not -> "Not"
        | Neg -> "Neg"
      in
      Fmt.pf ppf "@[<hov 2>Unop (%s,@ %a)@]" op_s dump_term t
  | Nil -> Fmt.string ppf "Nil"
  | ONone -> Fmt.string ppf "None"
  | OSome t -> Fmt.pf ppf "@[<hov 2>Some (%a)@]" dump_term t
  | Conj (t1, t2) -> Fmt.pf ppf "@[<hov 2>Conj (%a,@ %a)@]" dump_term t1 dump_term t2
  | Disj (t1, t2) -> Fmt.pf ppf "@[<hov 2>Disj (%a,@ %a)@]" dump_term t1 dump_term t2
  | Implies (t1, t2) -> Fmt.pf ppf "@[<hov 2>Implies (%a,@ %a)@]" dump_term t1 dump_term t2
  | Wand (t1, t2) -> Fmt.pf ppf "@[<hov 2>Wand (%a,@ %a)@]" dump_term t1 dump_term t2
  | Subsumes (t1, t2) -> Fmt.pf ppf "@[<hov 2>Subsumes (%a,@ %a)@]" dump_term t1 dump_term t2
  | Emp -> Fmt.string ppf "Emp"
  | PointsTo (t1, t2) -> Fmt.pf ppf "@[<hov 2>PointsTo (%a,@ %a)@]" dump_term t1 dump_term t2
  | SepConj (t1, t2) -> Fmt.pf ppf "@[<hov 2>SepConj (%a,@ %a)@]" dump_term t1 dump_term t2
  | Requires t -> Fmt.pf ppf "@[<hov 2>Requires (%a)@]" dump_term t
  | Ensures t -> Fmt.pf ppf "@[<hov 2>Ensures (%a)@]" dump_term t
  | Bind (s, b) ->
      let x, body = Bindlib.unbind b in
      Fmt.pf ppf "@[<hov 2>Bind (%a,@ %s.@ %a)@]" dump_term s (Bindlib.name_of x) dump_term body
  | Apply (f, ts) ->
      Fmt.pf ppf "@[<hov 2>Apply (%a,@ [%a])@]" dump_term f (Fmt.list ~sep:Fmt.comma dump_term) ts
  | Forall b ->
      let xs, body = Bindlib.unmbind b in
      let args = String.concat " " (Array.to_list (Array.map Bindlib.name_of xs)) in
      Fmt.pf ppf "@[<hov 2>Forall (%s.@ %a)@]" args dump_term body
  | Exists b ->
      let xs, body = Bindlib.unmbind b in
      let args = String.concat " " (Array.to_list (Array.map Bindlib.name_of xs)) in
      Fmt.pf ppf "@[<hov 2>Exists (%s.@ %a)@]" args dump_term body
  | Shift b ->
      let k, body = Bindlib.unbind b in
      Fmt.pf ppf "@[<hov 2>Shift (%s.@ %a)@]" (Bindlib.name_of k) dump_term body
  | Reset t -> Fmt.pf ppf "@[<hov 2>Reset (%a)@]" dump_term t
