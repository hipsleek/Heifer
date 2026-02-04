open Bindlib
open Unify
open Util
open Core.Syntax
open Core.Syntax_util
open Util.Snoc_list

exception Rewrite_failure of string

type rewrite_rule = {
  (* unification variables, collected to an array (mvar) *)
  rwr_umvar : term mvar;
  (* unification variables, collected to a set.
     Invariant: rwr_uvars = TVSets.of_array rwr_umvar *)
  rwr_uvars : TVSet.t;
  (* Invariant: rwr_arity = Array.length rwr_umvar *)
  rwr_arity : int;
  rwr_conditions : term list;
  (* unification variables that appear in the rewriting conditions. These unification variables
     must not be unified with any bound variable, otherwise the bound variable would escape its
     scope and we would have ill-formed conditions *)
  rwr_condition_uvars : TVSet.t;
  rwr_relation : [ `Eq | `Subsumes ];
  rwr_lhs : term;
  rwr_rhs : term;
  (* cached mbinder of rwr_conditions and rwr_rhs, for efficiency *)
  rwr_conditions_mbinder : (term, term list) mbinder;
  rwr_rhs_mbinder : (term, term) mbinder;
}

let make_rule ?(direction = `Ltr) t =
  let rec visit mvars conditions = function
    | Forall b ->
        let xs, t = unmbind b in
        visit (Snoc (mvars, xs)) conditions t
    | Implies (t1, t2) -> visit mvars (Snoc (conditions, t1)) t2
    | Subsumes (t1, t2) -> (mvars, conditions, `Subsumes, t1, t2)
    | Binop (Eq, t1, t2) -> (mvars, conditions, `Eq, t1, t2)
    | _ -> invalid_arg "prop_to_rule: cannot convert term to rewrite_rule"
  in
  let mvars, conditions, rwr_relation, t1, t2 = visit Lin Lin t in
  let rwr_umvar = Array.concat (Snoc_list.to_list mvars) in
  let rwr_uvars = TVSets.of_array rwr_umvar in
  let rwr_arity = Array.length rwr_umvar in
  let rwr_conditions = Snoc_list.to_list conditions in
  let rwr_condition_vars = List.fold_left pre_get_vars TVSet.empty rwr_conditions in
  let rwr_condition_uvars = TVSet.inter rwr_condition_vars rwr_uvars in
  let rwr_lhs, rwr_rhs =
    match direction with
    | `Ltr -> (t1, t2)
    | `Rtl -> (t2, t1)
  in
  let rwr_conditions_mbinder = mgeneralize_list rwr_umvar rwr_conditions in
  let rwr_rhs_mbinder = mgeneralize rwr_umvar rwr_rhs in
  {
    rwr_umvar;
    rwr_uvars;
    rwr_arity;
    rwr_conditions;
    rwr_condition_uvars;
    rwr_relation;
    rwr_lhs;
    rwr_rhs;
    rwr_conditions_mbinder;
    rwr_rhs_mbinder;
  }

let get_rule_relation rule = rule.rwr_relation
let get_rule_conditions rule = rule.rwr_conditions
let get_rule_lhs rule = rule.rwr_lhs
let get_rule_rhs rule = rule.rwr_rhs

type rewrite_state = {
  (* an accumulator of instantiated conditions *)
  rws_conditions : term snoc_list;
  (* number of rewriting done *)
  rws_count : int;
}

module Monad : sig
  type 'a t

  val run : 'a t -> rewrite_state -> 'a * rewrite_state
  val pure : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapl : 'b -> 'a t -> 'b t
  val lift2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t
  val ( <$ ) : 'b -> 'a t -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val get : rewrite_state t
  val put : rewrite_state -> unit t
  val modify : (rewrite_state -> rewrite_state) -> unit t
end = struct
  type 'a t = rewrite_state -> 'a * rewrite_state

  let run m = m
  let pure x sigma = (x, sigma)

  let map f m sigma =
    let x, sigma = m sigma in
    (f x, sigma)

  let mapl x m sigma =
    let _, sigma = m sigma in
    (x, sigma)

  let lift2 f m1 m2 sigma =
    let x, sigma = m1 sigma in
    let y, sigma = m2 sigma in
    (f x y, sigma)

  let bind m f sigma =
    let x, sigma = m sigma in
    let y, sigma = f x sigma in
    (y, sigma)

  let ( <$> ) = map
  let ( <$ ) = mapl
  let ( >>= ) = bind
  let ( let+ ) m f = map f m
  let ( let* ) = bind
  let get sigma = (sigma, sigma)
  let put sigma _ = ((), sigma)
  let modify f sigma = ((), f sigma)
end

let check_sigma_cardinal cardinal sigma =
  if TVMap.cardinal sigma <> cardinal then
    raise (Rewrite_failure "uninstantiated unification variables")

let check_uvars_well_scoped uvars bvars sigma =
  let check uvar =
    let t = TVMap.find uvar sigma in
    if has_vars bvars t then raise (Rewrite_failure "escaped variable")
  in
  TVSet.iter check uvars

(** Rewrite the target at the top level, either raising on failure or returning the rewritten target
*)
let pre_rewrite_root rule bvars target =
  let {
    rwr_umvar;
    rwr_arity;
    rwr_uvars;
    rwr_lhs;
    rwr_condition_uvars;
    rwr_conditions_mbinder;
    rwr_rhs_mbinder;
    _;
  } =
    rule
  in
  let sigma, frame =
    match unify_assoc rwr_lhs target rwr_uvars with
    | sigma, None -> (sigma, Fun.id)
    | sigma, Some frame -> (sigma, frame)
    | exception Unification_failure msg -> raise (Rewrite_failure msg)
  in
  check_sigma_cardinal rwr_arity sigma;
  check_uvars_well_scoped rwr_condition_uvars bvars sigma;
  let args = Array.map (fun x -> TVMap.find x sigma) rwr_umvar in
  (frame (msubst rwr_rhs_mbinder args), msubst rwr_conditions_mbinder args)

(** Traverse the target and rewrite using the given rule everywhere in it.

    This is unlike Rocq's rewriting using evars, where all occurrences subject to one evar
    instantiation are rewritten. The consequence is that a fixed number of subgoals is produced from
    the side conditions. In contarst, our scheme produces a number of side conditions/subgoals
    depending on the number of occurrences rewritten. This is because the instantiations are only
    discovered during traversal. *)
let rec pre_rewrite rule bvars target =
  let open Monad in
  try
    let result, conditions = pre_rewrite_root rule bvars target in
    let update { rws_conditions; rws_count } =
      let rws_conditions = Snoc_list.append_list rws_conditions conditions in
      let rws_count = rws_count + 1 in
      { rws_conditions; rws_count }
    in
    result <$ modify update
  with Rewrite_failure _ ->
    (match target with
    | Var _ | Symbol _ | Unit | True | False | Int _ | Nil | Emp -> pure target
    | Fun b -> Tm.fun_ <$> pre_rewrite_mbinder rule bvars b
    | Apply (f, t) -> lift2 Tm.apply (pre_rewrite rule bvars f) (pre_rewrite_list rule bvars t)
    | Tuple ts -> Tm.tuple <$> pre_rewrite_list rule bvars ts
    | Binop (op, t1, t2) ->
        lift2 (Tm.binop op) (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | Unop (op, t) -> Tm.unop op <$> pre_rewrite rule bvars t
    | Conj (t1, t2) -> lift2 Tm.conj (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | Disj (t1, t2) -> lift2 Tm.disj (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | Implies (t1, t2) -> lift2 Tm.implies (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | Wand (t1, t2) -> lift2 Tm.wand (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | Subsumes (t1, t2) -> lift2 Tm.subsumes (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | PointsTo (t1, t2) -> lift2 Tm.pointsto (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | SepConj (t1, t2) -> lift2 Tm.sepconj (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | Requires t -> Tm.requires <$> pre_rewrite rule bvars t
    | Ensures t -> Tm.ensures <$> pre_rewrite rule bvars t
    | Sequence (t1, t2) -> lift2 Tm.sequence (pre_rewrite rule bvars t1) (pre_rewrite rule bvars t2)
    | Bind (t, b) -> lift2 Tm.bind (pre_rewrite rule bvars t) (pre_rewrite_binder rule bvars b)
    | Forall b -> Tm.forall <$> pre_rewrite_mbinder rule bvars b
    | Exists b -> Tm.exists <$> pre_rewrite_mbinder rule bvars b
    | Shift b -> Tm.shift <$> pre_rewrite_binder rule bvars b
    | Reset t -> Tm.reset <$> pre_rewrite rule bvars t)

and pre_rewrite_list rule bvars target =
  let open Monad in
  match target with
  | [] -> pure []
  | t :: ts ->
      let* t = pre_rewrite rule bvars t in
      let* ts = pre_rewrite_list rule bvars ts in
      pure (t :: ts)

and pre_rewrite_binder rule bvars target =
  let open Monad in
  let x, target = unbind target in
  generalize x <$> pre_rewrite rule (TVSet.add x bvars) target

and pre_rewrite_mbinder rule bvars target =
  let open Monad in
  let xs, target = unmbind target in
  mgeneralize xs <$> pre_rewrite rule (TVSets.add_array xs bvars) target

let empty_rewrite_state = { rws_conditions = Lin; rws_count = 0 }

let rewrite rule target =
  let result, state = Monad.run (pre_rewrite rule TVSet.empty target) empty_rewrite_state in
  if state.rws_count = 0 then raise (Rewrite_failure "no progress");
  (result, Snoc_list.to_list state.rws_conditions)
