open Bindlib

(* type metavar = {mv_name : string} *)

type binop =
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Neq

type unop =
  | Not
  | Neg

(** Atomic term: variables, (literal) constants, functions, primitives *)
type term =
  | TVar of term var
  | TUnit
  | TTrue
  | TFalse
  | TInt of int
  | TFun of (term, staged_spec) binder
  | TTuple of term list
  | TBinop of binop * term * term
  | TUnop of unop * term
(* | TMetavar of metavar *)

(** Atomic pure proposition like `x < 1` will be represented with `term` and
    lifted to `prop` using `PAtom` *)
and prop =
  | PAtom of term
  | PConj of prop * prop

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

module Constructors = struct
  let new_tvar = new_var (fun v -> TVar v)
  let mk_tvar = box_var
  let mk_tunit = box TUnit
  let mk_ttrue = box TTrue
  let mk_tfalse = box TFalse
  let mk_tint i = box (TInt i)
  let mk_tbinop op = box_apply2 (fun a b -> TBinop (op, a, b))
  let mk_tunop op = box_apply (fun a -> TUnop (op, a))
  let mk_patom = box_apply (fun a -> PAtom a)
  let mk_pconj = box_apply2 (fun a b -> PConj (a, b))

  (* let mk_tpair = box_apply2 (fun t1 t2 -> TPair (t1, t2)) *)
  let mk_tfun = box_apply (fun b -> TFun b)
  let mk_hpure = box_apply (fun h -> HPure h)
  let mk_hemp = box HEmp
  let mk_hpointsto = box_apply2 (fun l v -> HPointsTo (l, v))
  let mk_hsepconj = box_apply2 (fun h1 h2 -> HSepConj (h1, h2))

  (* let mk_tmetavar mv = box (TMetavar mv) *)
  (* let mk_ststate = box StState *)
  (* let mk_stmetavar mv = box (StMetavar mv) *)
  let mk_return = box_apply (fun t -> Return t)
  let mk_requires = box_apply (fun p -> Requires p)
  let mk_ensures = box_apply (fun p -> Ensures p)
  let mk_sequence = box_apply2 (fun s1 s2 -> Sequence (s1, s2))
  let mk_bind = box_apply2 (fun s b -> Bind (s, b))
  let mk_apply = box_apply2 (fun f t -> Apply (f, t))
  let mk_disjunct = box_apply2 (fun s1 s2 -> Disjunct (s1, s2))
  let mk_exists = box_apply (fun b -> Exists b)
  let mk_shift = box_apply (fun b -> Shift b)
  let mk_reset = box_apply (fun s -> Reset s)
  let mk_dollar = box_apply2 (fun s k -> Dollar (s, k))
  (* let mk_smetavar mv = box (SMetavar mv) *)
  (* let mk_binder = box_apply (fun b -> Binder b) *)
  (* let mk_ignore = box_apply (fun s -> Ignore s) *)
  (* let mk_sbmetavar mv = box (SBMetavar mv) *)

  let rec box_term = function
    | TVar x -> mk_tvar x
    (* | TSymbol s -> mk_tsymbol s *)
    | TUnit -> mk_tunit
    (* | TBool b -> mk_tbool b *)
    | TInt i -> mk_tint i
    (* | TPair (t1, t2) -> mk_tpair (box_term t1) (box_term t2) *)
    | TFun b -> mk_tfun (box_binder box_staged_spec b)
    (* | TMetavar mv -> mk_tmetavar mv *)
    | TTrue -> mk_ttrue
    | TFalse -> mk_tfalse
    | TBinop (op, a, b) -> mk_tbinop op (box_term a) (box_term b)
    | TUnop (op, a) -> mk_tunop op (box_term a)
    | TTuple _ -> failwith "box_term: todo"

  and box_prop = function
    | PAtom p -> mk_patom (box_term p)
    | PConj (a, b) -> mk_pconj (box_prop a) (box_prop b)

  and box_hprop = function
    | HEmp -> mk_hemp
    | HPure p -> mk_hpure (box_prop p)
    | HPointsTo (l, v) -> mk_hpointsto (box_term l) (box_term v)
    | HSepConj (h1, h2) -> mk_hsepconj (box_hprop h1) (box_hprop h2)

  and box_staged_spec = function
    | Return t -> mk_return (box_term t)
    (* | Ensures st -> mk_ensures (box_state st) *)
    | Sequence (s1, s2) -> mk_sequence (box_staged_spec s1) (box_staged_spec s2)
    | Bind (s, b) -> mk_bind (box_staged_spec s) (box_binder box_staged_spec b)
    | Apply (f, t) -> mk_apply (box_term f) (box_term t)
    | Disjunct (s1, s2) -> mk_disjunct (box_staged_spec s1) (box_staged_spec s2)
    | Exists b -> mk_exists (box_binder box_staged_spec b)
    | Shift b -> mk_shift (box_binder box_staged_spec b)
    | Reset s -> mk_reset (box_staged_spec s)
    | Dollar (s, k) ->
      mk_dollar (box_staged_spec s) (box_binder box_staged_spec k)
    (* | SMetavar mv -> mk_smetavar mv *)
    | Requires h -> mk_requires (box_hprop h)
    | Ensures h -> mk_ensures (box_hprop h)
    | Forall _ -> failwith "box_staged_spec: todo"

  (* and box_staged_spec_binder = function
    | Binder b -> mk_binder (box_binder box_staged_spec b)
    | Ignore s -> mk_ignore (box_staged_spec s)
    | SBMetavar mv -> mk_sbmetavar mv *)
end

(* module StagedSpecBinder = struct
  let subst (b : staged_spec_binder) (t : term) : staged_spec =
    match b with
    | Binder b -> subst b t
    | Ignore s -> s
    | SBMetavar _ -> assert false

  let compose ~(delimited : bool) (b : staged_spec_binder) (s : staged_spec) :
      staged_spec =
    if delimited then Dollar (s, b)
    else
      match b with
      | Binder _ -> Bind (s, b)
      | Ignore s' -> Sequence (s, s')
      | SBMetavar _ -> assert false
end

module Metavar = struct
  type t = metavar

  let equal (mv1 : t) (mv2 : t) = String.equal mv1.mv_name mv2.mv_name
  let compare (mv1 : t) (mv2 : t) = String.compare mv1.mv_name mv2.mv_name
  let hash (mv : t) = String.hash mv.mv_name
end

module Symbol = struct
  type t = symbol

  let equal (s1 : t) (s2 : t) = String.equal s1.s_name s2.s_name
  let compare (s1 : t) (s2 : t) = String.compare s1.s_name s2.s_name
  let hash (s : t) = String.hash s.s_name
end

module Sort = struct
  exception Invalid_sort of string
  exception Sort_mismatch of string

  let invalid_sort msg = raise (Invalid_sort msg)
  let sort_mismatch msg = raise (Sort_mismatch msg)
end *)
