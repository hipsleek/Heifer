open Bindlib

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
  | Times
  | Cons

type unop =
  | Not
  | Neg

(** Atomic term: variables, (literal) constants, functions, primitives. We
    enforce that [term] must be pure: no side-effect can happen when reducing a
    term. *)
type term =
  | TVar of term var
  | TSymbol of symbol
  | TUnit
  | TTrue
  | TFalse
  | TInt of int
  | TFun of (term, staged_spec) binder
  | TApp of string * term list
  | TTuple of term list
  | TBinop of binop * term * term
  | TUnop of unop * term
  | TNil
(* | TMetavar of metavar *)

(** Atomic pure proposition like [x < 1] will be represented with [term] and
    lifted to [prop] using [PAtom]. *)
and prop =
  | PAtom of term
  | PConj of prop * prop
  | PImplies of prop * prop
  | PForall of (term, prop) binder
  | PSubsumes of staged_spec * staged_spec

and hprop =
  | HPure of prop
  | HEmp
  | HPointsTo of term * term
  | HSepConj of hprop * hprop

and staged_spec =
  | Return of term
  | Requires of hprop
  | Ensures of hprop
  | Sequence of staged_spec * staged_spec
  | Bind of staged_spec * (term, staged_spec) binder
  | Apply of term * term
  | Disjunct of staged_spec * staged_spec
  | Forall of (term, staged_spec) binder
  | Exists of (term, staged_spec) binder
  | Shift of (term, staged_spec) binder
  | Reset of staged_spec
  | Dollar of staged_spec * (term, staged_spec) binder
(* | SMetavar of metavar *)

(** Top level declaration.

    [Dfun] declares a possibly recursive function. *)
type decl =
  | Dfun of (term, staged_spec) binder (* TODO: use mbinder if possible *)

(** Smart constructors that wraps data in [Bindlib.box]. This module should
    never be [open]. Functions inside this module should be called by prefixing
    the function's name with [Mk]. *)
module Mk = struct
  let tvar = box_var
  let tsymbol sym = box (TSymbol sym)
  let tunit = box TUnit
  let tnil = box TNil
  let ttrue = box TTrue
  let tfalse = box TFalse
  let tapp = box_apply2 (fun f xs -> TApp (f, xs))
  let tint i = box (TInt i)
  let ttuple = box_apply (fun ts -> TTuple ts)
  let tfun = box_apply (fun b -> TFun b)
  let tbinop op = box_apply2 (fun t1 t2 -> TBinop (op, t1, t2))
  let tunop op = box_apply (fun t -> TUnop (op, t))

  (* let tmetavar mv = box (TMetavar mv) *)
  let patom = box_apply (fun t -> PAtom t)
  let pconj = box_apply2 (fun p1 p2 -> PConj (p1, p2))
  let pforall = box_apply (fun b -> PForall b)
  let pimplies = box_apply2 (fun p1 p2 -> PImplies (p1, p2))
  let psubsumes = box_apply2 (fun f1 f2 -> PSubsumes (f1, f2))
  let hpure = box_apply (fun p -> HPure p)
  let hemp = box HEmp
  let hpointsto = box_apply2 (fun t1 t2 -> HPointsTo (t1, t2))
  let hsepconj = box_apply2 (fun p1 p2 -> HSepConj (p1, p2))

  (* let stmetavar mv = box (StMetavar mv) *)
  let return = box_apply (fun t -> Return t)
  let requires = box_apply (fun p -> Requires p)
  let ensures = box_apply (fun p -> Ensures p)
  let sequence = box_apply2 (fun s1 s2 -> Sequence (s1, s2))
  let bind = box_apply2 (fun s b -> Bind (s, b))
  let apply = box_apply2 (fun f t -> Apply (f, t))
  let disjunct = box_apply2 (fun s1 s2 -> Disjunct (s1, s2))
  let forall = box_apply (fun b -> Forall b)
  let exists = box_apply (fun b -> Exists b)
  let shift = box_apply (fun b -> Shift b)
  let reset = box_apply (fun s -> Reset s)
  let dollar = box_apply2 (fun s k -> Dollar (s, k))
  (* let smetavar mv = box (SMetavar mv) *)
  (* let sbmetavar mv = box (SBMetavar mv) *)
end

let new_tvar = new_var (fun v -> TVar v)

let rec box_term = function
  | TVar x -> Mk.tvar x
  | TSymbol sym -> Mk.tsymbol sym
  | TUnit -> Mk.tunit
  | TNil -> Mk.tnil
  | TTrue -> Mk.ttrue
  | TFalse -> Mk.tfalse
  | TApp (f, xs) -> Mk.tapp (box f) (box_list (List.map box_term xs))
  | TInt i -> Mk.tint i
  | TTuple ts -> Mk.ttuple (box_list (List.map box_term ts))
  | TFun b -> Mk.tfun (box_binder box_staged_spec b)
  | TBinop (op, t1, t2) -> Mk.tbinop op (box_term t1) (box_term t2)
  | TUnop (op, t) -> Mk.tunop op (box_term t)
(* | TMetavar mv -> tmetavar mv *)
(* | _ -> failwith "box_term: todo" *)

and box_prop = function
  | PAtom t -> Mk.patom (box_term t)
  | PConj (p1, p2) -> Mk.pconj (box_prop p1) (box_prop p2)
  | PForall b -> Mk.pforall (box_binder box_prop b)
  | PSubsumes (f1, f2) -> Mk.psubsumes (box_staged_spec f1) (box_staged_spec f2)
  | PImplies (p1, p2) -> Mk.pimplies (box_prop p1) (box_prop p2)

and box_hprop = function
  | HPure p -> Mk.hpure (box_prop p)
  | HEmp -> Mk.hemp
  | HPointsTo (t1, t2) -> Mk.hpointsto (box_term t1) (box_term t2)
  | HSepConj (p1, p2) -> Mk.hsepconj (box_hprop p1) (box_hprop p2)

and box_staged_spec = function
  | Return t -> Mk.return (box_term t)
  | Requires p -> Mk.requires (box_hprop p)
  | Ensures p -> Mk.ensures (box_hprop p)
  | Sequence (s1, s2) -> Mk.sequence (box_staged_spec s1) (box_staged_spec s2)
  | Bind (s, b) -> Mk.bind (box_staged_spec s) (box_binder box_staged_spec b)
  | Apply (f, t) -> Mk.apply (box_term f) (box_term t)
  | Disjunct (s1, s2) -> Mk.disjunct (box_staged_spec s1) (box_staged_spec s2)
  | Forall b -> Mk.forall (box_binder box_staged_spec b)
  | Exists b -> Mk.exists (box_binder box_staged_spec b)
  | Shift b -> Mk.shift (box_binder box_staged_spec b)
  | Reset s -> Mk.reset (box_staged_spec s)
  | Dollar (s, k) ->
    Mk.dollar (box_staged_spec s) (box_binder box_staged_spec k)
(* | SMetavar mv -> smetavar mv *)
(* | _ -> failwith "box_staged_spec: todo" *)

type sort =
  | Sort_term
  | Sort_prop
  | Sort_hprop
  | Sort_staged_spec

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
  | TVar x1, TVar x2 -> eq_vars x1 x2
  | TSymbol s1, TSymbol s2 -> s1.sym_name = s2.sym_name
  | TUnit, TUnit -> true
  | TTrue, TTrue -> true
  | TFalse, TFalse -> true
  | TInt i1, TInt i2 -> i1 = i2
  | TFun b1, TFun b2 -> eq_binder equal_staged_spec b1 b2
  | TApp (f1, xs1), TApp (f2, xs2) ->
    f1 = f2
    && List.length xs1 = List.length xs2
    && List.for_all2 equal_term xs1 xs2
  | TTuple ts1, TTuple ts2 ->
    List.length ts1 = List.length ts2 && List.for_all2 equal_term ts1 ts2
  | TBinop (op1, t11, t12), TBinop (op2, t21, t22) ->
    op1 = op2 && equal_term t11 t21 && equal_term t12 t22
  | TUnop (op1, t1), TUnop (op2, t2) -> op1 = op2 && equal_term t1 t2
  | TNil, TNil -> true
  | _, _ -> false

and equal_prop p1 p2 =
  match (p1, p2) with
  | PAtom t1, PAtom t2 -> equal_term t1 t2
  | PConj (p11, p12), PConj (p21, p22) ->
    equal_prop p11 p21 && equal_prop p12 p22
  | PImplies (p11, p12), PImplies (p21, p22) ->
    equal_prop p11 p21 && equal_prop p12 p22
  | PSubsumes (s11, s12), PSubsumes (s21, s22) ->
    equal_staged_spec s11 s21 && equal_staged_spec s12 s22
  | _, _ -> false

and equal_hprop h1 h2 =
  match (h1, h2) with
  | HPure p1, HPure p2 -> equal_prop p1 p2
  | HEmp, HEmp -> true
  | HPointsTo (t11, t12), HPointsTo (t21, t22) ->
    equal_term t11 t21 && equal_term t12 t22
  | HSepConj (h11, h12), HSepConj (h21, h22) ->
    equal_hprop h11 h21 && equal_hprop h12 h22
  | _, _ -> false

and equal_staged_spec s1 s2 =
  match (s1, s2) with
  | Return t1, Return t2 -> equal_term t1 t2
  | Requires h1, Requires h2 -> equal_hprop h1 h2
  | Ensures h1, Ensures h2 -> equal_hprop h1 h2
  | Sequence (s11, s12), Sequence (s21, s22) ->
    equal_staged_spec s11 s21 && equal_staged_spec s12 s22
  | Bind (s1, b1), Bind (s2, b2) ->
    equal_staged_spec s1 s2 && eq_binder equal_staged_spec b1 b2
  | Apply (t11, t12), Apply (t21, t22) ->
    equal_term t11 t21 && equal_term t12 t22
  | Disjunct (s11, s12), Disjunct (s21, s22) ->
    equal_staged_spec s11 s21 && equal_staged_spec s12 s22
  | Forall b1, Forall b2 -> eq_binder equal_staged_spec b1 b2
  | Exists b1, Exists b2 -> eq_binder equal_staged_spec b1 b2
  | Shift b1, Shift b2 -> eq_binder equal_staged_spec b1 b2
  | Reset s1, Reset s2 -> equal_staged_spec s1 s2
  | Dollar (s1, k1), Dollar (s2, k2) ->
    equal_staged_spec s1 s2 && eq_binder equal_staged_spec k1 k2
  | _, _ -> false
