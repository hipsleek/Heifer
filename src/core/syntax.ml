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

(** Atomic term: variables, (literal) constants, functions, primitives. We
    enforce that [term] must be pure: no side-effect can happen when reducing a
    term. *)
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

(** Atomic pure proposition like [x < 1] will be represented with [term] and
    lifted to [prop] using [PAtom]. *)
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

(** Smart constructors that wraps data in [Bindlib.box]. This module should
    never be [open]. Functions inside this module should be called by prefixing
    the function's name with [Mk]. *)
module Mk = struct
  let tvar = box_var
  let tunit = box TUnit
  let ttrue = box TTrue
  let tfalse = box TFalse
  let tint i = box (TInt i)
  let ttuple = box_apply (fun ts -> TTuple ts)
  let tfun = box_apply (fun b -> TFun b)
  let tbinop op = box_apply2 (fun t1 t2 -> TBinop (op, t1, t2))
  let tunop op = box_apply (fun t -> TUnop (op, t))

  (* let tmetavar mv = box (TMetavar mv) *)
  let patom = box_apply (fun t -> PAtom t)
  let pconj = box_apply2 (fun p1 p2 -> PConj (p1, p2))
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
  | TUnit -> Mk.tunit
  | TTrue -> Mk.ttrue
  | TFalse -> Mk.tfalse
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
