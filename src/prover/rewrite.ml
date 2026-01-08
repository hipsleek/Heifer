open Bindlib
open Unify
open Core.Syntax

exception Rewrite_failure

type rule = (term, staged_spec * staged_spec) mbinder

let rewrite_exact rule target : staged_spec =
  let uvars, (lhs, rhs) = unmbind rule in
  let sigma =
    try unify lhs target (TVSet.of_seq (Array.to_seq uvars))
    with Unification_failure -> raise Rewrite_failure
  in
  if TVMap.cardinal sigma <> Array.length uvars then raise Rewrite_failure;
  let args = Array.map (fun x -> TVMap.find x sigma) uvars in
  let rhs = unbox (bind_mvar uvars (box_staged_spec rhs)) in
  msubst rhs args

(** Traverse the target, and rewrite if possible. *)
let rec rewrite rule target : staged_spec =
  try
    rewrite_exact rule target
  with Rewrite_failure ->
    match target with
    | Return t -> Return t
    | Requires p -> Requires p
    | Ensures p -> Ensures p
    | Sequence (s1, s2) -> Sequence (rewrite rule s1, rewrite rule s2)
    | Bind (s, b) -> Bind (rewrite rule s, rewrite_binder rule b)
    | Apply (f, t) -> Apply (f, t)
    | Disjunct (s1, s2) -> Disjunct (rewrite rule s1, rewrite rule s2)
    | Forall b -> Forall (rewrite_binder rule b)
    | Exists b -> Exists (rewrite_binder rule b)
    | Shift b -> Shift (rewrite_binder rule b)
    | Reset s -> Reset (rewrite rule s)
    | Dollar _ -> failwith "todo"
and rewrite_binder rule target : (term, staged_spec) binder =
  let x, target = unbind target in
  unbox (bind_var x (box_staged_spec (rewrite rule target)))
