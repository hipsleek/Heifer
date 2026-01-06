open Bindlib

(* type metavar = {mv_name : string} *)

type binop = Lt | Le | Gt | Ge | Eq | Neq

type unop = Not | Neg

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

(** Atomic pure proposition like `x < 1` will be represented with `term` and lifted to `prop` using `PAtom` *)
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
  (* let mk_tpair = box_apply2 (fun t1 t2 -> TPair (t1, t2)) *)
  let mk_ttuple = box_apply (fun ts -> TTuple ts)
  let mk_tfun = box_apply (fun b -> TFun b)
  let mk_tbinop op = box_apply2 (fun t1 t2 -> TBinop (op, t1, t2))
  let mk_tunop op = box_apply (fun t -> TUnop (op, t))
  (* let mk_tmetavar mv = box (TMetavar mv) *)
  let mk_patom = box_apply (fun t -> PAtom t)
  let mk_pconj = box_apply2 (fun p1 p2 -> PConj (p1, p2))
  let mk_hpure = box_apply (fun p -> HPure p)
  let mk_hemp = box HEmp
  let mk_hpointsto = box_apply2 (fun t1 t2 -> HPointsTo (t1, t2))
  let mk_hsepconj = box_apply2 (fun p1 p2 -> HSepConj (p1, p2))
  (* let mk_stmetavar mv = box (StMetavar mv) *)
  let mk_return = box_apply (fun t -> Return t)
  let mk_requires = box_apply (fun p -> Requires p)
  let mk_ensures = box_apply (fun p -> Ensures p)
  let mk_sequence = box_apply2 (fun s1 s2 -> Sequence (s1, s2))
  let mk_bind = box_apply2 (fun s b -> Bind (s, b))
  let mk_apply = box_apply2 (fun f t -> Apply (f, t))
  let mk_disjunct = box_apply2 (fun s1 s2 -> Disjunct (s1, s2))
  let mk_forall = box_apply (fun b -> Forall b)
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
    | TUnit -> mk_tunit
    | TTrue -> mk_ttrue
    | TFalse -> mk_tfalse
    | TInt i -> mk_tint i
    | TTuple ts -> mk_ttuple (box_list (List.map box_term ts))
    | TFun b -> mk_tfun (box_binder box_staged_spec b)
    | TBinop (op, t1, t2) -> mk_tbinop op (box_term t1) (box_term t2)
    | TUnop (op, t) -> mk_tunop op (box_term t)
    (* | TMetavar mv -> mk_tmetavar mv *)
    (* | _ -> failwith "box_term: todo" *)

  and box_prop = function
    | PAtom t -> mk_patom (box_term t)
    | PConj (p1, p2) -> mk_pconj (box_prop p1) (box_prop p2)

  and box_hprop = function
    | HPure p -> mk_hpure (box_prop p)
    | HEmp -> mk_hemp
    | HPointsTo (t1, t2) -> mk_hpointsto (box_term t1) (box_term t2)
    | HSepConj (p1, p2) -> mk_hsepconj (box_hprop p1) (box_hprop p2)

  and box_staged_spec = function
    | Return t -> mk_return (box_term t)
    | Requires p -> mk_requires (box_hprop p)
    | Ensures p -> mk_ensures (box_hprop p)
    | Sequence (s1, s2) -> mk_sequence (box_staged_spec s1) (box_staged_spec s2)
    | Bind (s, b) -> mk_bind (box_staged_spec s) (box_binder box_staged_spec b)
    | Apply (f, t) -> mk_apply (box_term f) (box_term t)
    | Disjunct (s1, s2) -> mk_disjunct (box_staged_spec s1) (box_staged_spec s2)
    | Forall b -> mk_forall (box_binder box_staged_spec b)
    | Exists b -> mk_exists (box_binder box_staged_spec b)
    | Shift b -> mk_shift (box_binder box_staged_spec b)
    | Reset s -> mk_reset (box_staged_spec s)
    | Dollar (s, k) -> mk_dollar (box_staged_spec s) (box_binder box_staged_spec k)
    (* | SMetavar mv -> mk_smetavar mv *)
    (* | _ -> failwith "box_staged_spec: todo" *)
end

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
