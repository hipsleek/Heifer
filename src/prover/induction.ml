open Bindlib
open Core.Syntax
open Core.Syntax_util

type induction_hypothesis = (term, prop) mbinder

let build_wf_premise wf x y =
  match wf with
  | `List -> Mk.(apply (symbol { sym_name = "sublist" }) (box_list [box_var y; box_var x]))
  | `Int n ->
      let ge = Mk.(binop Ge (box_var y) (int n)) in
      let lt = Mk.(binop Lt (box_var y) (box_var x)) in
      Mk.conj ge lt

let induction wf x other_vars assumptions lhs rhs =
  (* TODO generalize over heap context *)
  let generalized_assumptions =
    let other_vars = TVSet.of_seq (Array.to_seq other_vars) in
    List.filter (has_vars (TVSet.add x other_vars)) assumptions
  in
  let ih =
    List.fold_right (fun h g -> Implies (h, g)) generalized_assumptions (Subsumes (lhs, rhs))
  in

  (* y is the new variable contained to be well-founded wrt x *)
  let y : term var = new_tvar (name_of (x : term var)) in

  (* replace uses of x in IH with y *)
  let ih = subst (unbox (bind_var x (box_term ih))) (unbox (box_var y)) in

  (* x no longer occurs in ih *)
  let gvars = Array.concat [[| y |]; other_vars] in

  let wf_premise = build_wf_premise wf x y in

  (* now generalize ih *)
  unbox (bind_mvar gvars (Mk.implies wf_premise (box_term ih)))
