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

(** Atomic term: variables, (literal) constants, functions, primitives;
    propositions; heap propositions; and staged specification formulae. *)
type term =
  | Var of term var
  | Symbol of symbol
  | Unit
  | True
  | False
  | Int of int
  | Fun of (term, term) mbinder
  | Tuple of term list
  | Binop of binop * term * term
  | Unop of unop * term
  | Nil
  | Conj of term * term
  | Disj of term * term
  | Implies of term * term
  | Subsumes of term * term
  | Emp
  | PointsTo of term * term
  | SepConj of term * term
  | Requires of term
  | Ensures of term
  | Sequence of term * term
  | Bind of term * (term, term) binder
  | Apply of term * term list
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
  let conj t1 t2 = Conj (t1, t2)
  let disj t1 t2 = Disj (t1, t2)
  let implies t1 t2 = Implies (t1, t2)
  let subsumes t1 t2 = Subsumes (t1, t2)
  let emp = Emp
  let pointsto t1 t2 = PointsTo (t1, t2)
  let sepconj t1 t2 = SepConj (t1, t2)
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
  let true_ = box True
  let false_ = box False
  let int i = box (Int i)
  let tuple = box_apply (fun ts -> Tuple ts)
  let fun_ = box_apply (fun b -> Fun b)
  let apply = box_apply2 (fun f xs -> Apply (f, xs))
  let binop op = box_apply2 (fun t1 t2 -> Binop (op, t1, t2))
  let unop op = box_apply (fun t -> Unop (op, t))
  let conj = box_apply2 (fun p1 p2 -> Conj (p1, p2))
  let disj = box_apply2 (fun s1 s2 -> Disj (s1, s2))
  let implies = box_apply2 (fun p1 p2 -> Implies (p1, p2))
  let subsumes = box_apply2 (fun f1 f2 -> Subsumes (f1, f2))
  let emp = box Emp
  let pointsto = box_apply2 (fun t1 t2 -> PointsTo (t1, t2))
  let sepconj = box_apply2 (fun p1 p2 -> SepConj (p1, p2))
  let requires = box_apply (fun p -> Requires p)
  let ensures = box_apply (fun p -> Ensures p)
  let sequence = box_apply2 (fun s1 s2 -> Sequence (s1, s2))
  let bind = box_apply2 (fun s b -> Bind (s, b))
  let forall = box_apply (fun b -> Forall b)
  let exists = box_apply (fun b -> Exists b)
  let shift = box_apply (fun b -> Shift b)
  let reset = box_apply (fun s -> Reset s)
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

  let ens_seq h f = Sequence (Ensures h, f)
  let req_seq h f = Sequence (Ensures h, f)
  let eq t1 t2 = Binop (Eq, t1, t2)
end

let new_tvar = new_var (fun v -> Var v)

let rec box_term = function
  | Var x -> Mk.var x
  | Symbol sym -> Mk.symbol sym
  | Unit -> Mk.unit
  | Nil -> Mk.nil
  | True -> Mk.true_
  | False -> Mk.false_
  | Apply (f, xs) -> Mk.apply (box_term f) (box_list (List.map box_term xs))
  | Int i -> Mk.int i
  | Tuple ts -> Mk.tuple (box_list (List.map box_term ts))
  | Fun b -> Mk.fun_ (box_mbinder box_term b)
  | Binop (op, t1, t2) -> Mk.binop op (box_term t1) (box_term t2)
  | Unop (op, t) -> Mk.unop op (box_term t)
  | Conj (p1, p2) -> Mk.conj (box_term p1) (box_term p2)
  | Disj (p1, p2) -> Mk.disj (box_term p1) (box_term p2)
  | Implies (p1, p2) -> Mk.implies (box_term p1) (box_term p2)
  | Subsumes (f1, f2) -> Mk.subsumes (box_term f1) (box_term f2)
  | Emp -> Mk.emp
  | PointsTo (t1, t2) -> Mk.pointsto (box_term t1) (box_term t2)
  | SepConj (p1, p2) -> Mk.sepconj (box_term p1) (box_term p2)
  | Requires p -> Mk.requires (box_term p)
  | Ensures p -> Mk.ensures (box_term p)
  | Sequence (s1, s2) -> Mk.sequence (box_term s1) (box_term s2)
  | Bind (s, b) -> Mk.bind (box_term s) (box_binder box_term b)
  | Forall b -> Mk.forall (box_mbinder box_term b)
  | Exists b -> Mk.exists (box_mbinder box_term b)
  | Shift b -> Mk.shift (box_binder box_term b)
  | Reset s -> Mk.reset (box_term s)

type prop = term
type hprop = term
type staged_spec = term

type sort =
  | Sort_term
  | Sort_prop
  | Sort_hprop
  | Sort_staged_spec

let pp_sort ppf t =
  match t with
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
  | Symbol s1, Symbol s2 -> s1 = s2
  | Unit, Unit -> true
  | True, True -> true
  | False, False -> true
  | Int i1, Int i2 -> i1 = i2
  | Fun b1, Fun b2 -> eq_mbinder equal_term b1 b2
  | Apply (f1, xs1), Apply (f2, xs2) ->
      equal_term f1 f2
      && List.length xs1 = List.length xs2
      && List.for_all2 equal_term xs1 xs2
  | Tuple ts1, Tuple ts2 ->
      List.length ts1 = List.length ts2 && List.for_all2 equal_term ts1 ts2
  | Binop (op1, t11, t12), Binop (op2, t21, t22) ->
      op1 = op2 && equal_term t11 t21 && equal_term t12 t22
  | Unop (op1, t1), Unop (op2, t2) -> op1 = op2 && equal_term t1 t2
  | Nil, Nil -> true
  | Conj (p11, p12), Conj (p21, p22) -> equal_term p11 p21 && equal_term p12 p22
  | Disj (p11, p12), Disj (p21, p22) -> equal_term p11 p21 && equal_term p12 p22
  | Implies (p11, p12), Implies (p21, p22) ->
      equal_term p11 p21 && equal_term p12 p22
  | Subsumes (s11, s12), Subsumes (s21, s22) ->
      equal_term s11 s21 && equal_term s12 s22
  | Emp, Emp -> true
  | PointsTo (t11, t12), PointsTo (t21, t22) ->
      equal_term t11 t21 && equal_term t12 t22
  | SepConj (h11, h12), SepConj (h21, h22) ->
      equal_term h11 h21 && equal_term h12 h22
  | Requires h1, Requires h2 -> equal_term h1 h2
  | Ensures h1, Ensures h2 -> equal_term h1 h2
  | Sequence (s11, s12), Sequence (s21, s22) ->
      equal_term s11 s21 && equal_term s12 s22
  | Bind (s1, b1), Bind (s2, b2) ->
      equal_term s1 s2 && eq_binder equal_term b1 b2
  | Forall b1, Forall b2 -> eq_mbinder equal_term b1 b2
  | Exists b1, Exists b2 -> eq_mbinder equal_term b1 b2
  | Shift b1, Shift b2 -> eq_binder equal_term b1 b2
  | Reset s1, Reset s2 -> equal_term s1 s2
  | _, _ -> false

let rec dump_term ppf t =
  match t with
  | Sequence (a, b) ->
      Fmt.pf ppf "@[<hov 2>Sequence (%a,@ %a)@]" dump_term a dump_term b
  | Var x -> Fmt.pf ppf "@[<hov 2>Var %s@]" (Bindlib.name_of x)
  | Symbol s -> Fmt.pf ppf "@[<hov 2>Symbol %s@]" s.sym_name
  | Unit -> Fmt.string ppf "Unit"
  | True -> Fmt.string ppf "True"
  | False -> Fmt.string ppf "False"
  | Int i -> Fmt.pf ppf "@[<hov 2>Int %d@]" i
  | Fun b ->
      let xs, body = Bindlib.unmbind b in
      let args =
        String.concat " " (Array.to_list (Array.map Bindlib.name_of xs))
      in
      Fmt.pf ppf "@[<hov 2>Fun (%s.@ %a)@]" args dump_term body
  | Tuple ts ->
      Fmt.pf ppf "@[<hov 2>Tuple [%a]@]" (Fmt.list ~sep:Fmt.comma dump_term) ts
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
      Fmt.pf ppf "@[<hov 2>Binop (%s,@ %a,@ %a)@]" op_s dump_term t1 dump_term
        t2
  | Unop (op, t) ->
      let op_s =
        match op with
        | Not -> "Not"
        | Neg -> "Neg"
      in
      Fmt.pf ppf "@[<hov 2>Unop (%s,@ %a)@]" op_s dump_term t
  | Nil -> Fmt.string ppf "Nil"
  | Conj (t1, t2) ->
      Fmt.pf ppf "@[<hov 2>Conj (%a,@ %a)@]" dump_term t1 dump_term t2
  | Disj (t1, t2) ->
      Fmt.pf ppf "@[<hov 2>Disj (%a,@ %a)@]" dump_term t1 dump_term t2
  | Implies (t1, t2) ->
      Fmt.pf ppf "@[<hov 2>Implies (%a,@ %a)@]" dump_term t1 dump_term t2
  | Subsumes (t1, t2) ->
      Fmt.pf ppf "@[<hov 2>Subsumes (%a,@ %a)@]" dump_term t1 dump_term t2
  | Emp -> Fmt.string ppf "Emp"
  | PointsTo (t1, t2) ->
      Fmt.pf ppf "@[<hov 2>PointsTo (%a,@ %a)@]" dump_term t1 dump_term t2
  | SepConj (t1, t2) ->
      Fmt.pf ppf "@[<hov 2>SepConj (%a,@ %a)@]" dump_term t1 dump_term t2
  | Requires t -> Fmt.pf ppf "@[<hov 2>Requires (%a)@]" dump_term t
  | Ensures t -> Fmt.pf ppf "@[<hov 2>Ensures (%a)@]" dump_term t
  | Bind (s, b) ->
      let x, body = Bindlib.unbind b in
      Fmt.pf ppf "@[<hov 2>Bind (%a,@ %s.@ %a)@]" dump_term s
        (Bindlib.name_of x) dump_term body
  | Apply (f, ts) ->
      Fmt.pf ppf "@[<hov 2>Apply (%a,@ [%a])@]" dump_term f
        (Fmt.list ~sep:Fmt.comma dump_term)
        ts
  | Forall b ->
      let xs, body = Bindlib.unmbind b in
      let args =
        String.concat " " (Array.to_list (Array.map Bindlib.name_of xs))
      in
      Fmt.pf ppf "@[<hov 2>Forall (%s.@ %a)@]" args dump_term body
  | Exists b ->
      let xs, body = Bindlib.unmbind b in
      let args =
        String.concat " " (Array.to_list (Array.map Bindlib.name_of xs))
      in
      Fmt.pf ppf "@[<hov 2>Exists (%s.@ %a)@]" args dump_term body
  | Shift b ->
      let k, body = Bindlib.unbind b in
      Fmt.pf ppf "@[<hov 2>Shift (%s.@ %a)@]" (Bindlib.name_of k) dump_term body
  | Reset t -> Fmt.pf ppf "@[<hov 2>Reset (%a)@]" dump_term t
