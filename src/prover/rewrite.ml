open Bindlib
open Unify
open Core.Syntax

exception Rewrite_failure

type rule = (term, staged_spec * staged_spec) mbinder

let rewrite_exact rule target : staged_spec =
  let xs, (lhs, rhs) = unmbind rule in
  let sigma =
    try unify_staged_spec lhs target
    with Unification_failure -> raise Rewrite_failure
  in
  if TVMap.cardinal sigma <> Array.length xs then raise Rewrite_failure;
  let args = Array.map (fun x -> TVMap.find x sigma) xs in
  let rhs = unbox (bind_mvar xs (box_staged_spec rhs)) in
  msubst rhs args

(** Traverse the target, and rewrite if possible. *)
let rewrite rule target =
  ignore (rule, target)
