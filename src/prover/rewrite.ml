open Bindlib
open Unify
open Core.Syntax

exception Rewrite_failure

type rule = (term, staged_spec * staged_spec) mbinder

let rec prop_to_rule_aux p ms =
  match p with
  | Forall b ->
      let xs, p = unmbind b in
      prop_to_rule_aux p (xs :: ms)
  | Subsumes (lhs, rhs) -> (List.rev ms, lhs, rhs)
  | _ -> failwith "prop_to_rule_aux: expect Forall and Subsumes only"

let prop_to_rule p =
  let ms, lhs, rhs = prop_to_rule_aux p [] in
  unbox
    (bind_mvar (Array.concat ms)
       (box_pair (box_staged_spec lhs) (box_staged_spec rhs)))

(** Check type of target *)
let rewrite_exact rule target =
  let uvars, (lhs, rhs) = unmbind rule in
  let sigma =
    try unify lhs target (TVSet.of_seq (Array.to_seq uvars))
    with Unification_failure -> raise Rewrite_failure
  in
  if TVMap.cardinal sigma <> Array.length uvars then raise Rewrite_failure;
  let args = Array.map (fun x -> TVMap.find x sigma) uvars in
  let rhs = unbox (bind_mvar uvars (box_staged_spec rhs)) in
  msubst rhs args

(** Traverse the target, and rewrite if possible.

    TODO: make this more efficient: repeated `unmbind` is inefficient *)
let rec rewrite rule target =
  try rewrite_exact rule target
  with Rewrite_failure ->
    (match target with
    | Requires p -> Requires p
    | Ensures p -> Ensures p
    | Sequence (s1, s2) -> Sequence (rewrite rule s1, rewrite rule s2)
    | Bind (s, b) -> Bind (rewrite rule s, rewrite_binder rule b)
    | Apply (f, t) -> Apply (f, t)
    | Disj (s1, s2) -> Disj (rewrite rule s1, rewrite rule s2)
    | Forall b -> Forall (rewrite_mbinder rule b)
    | Exists b -> Exists (rewrite_mbinder rule b)
    | Shift b -> Shift (rewrite_binder rule b)
    | Reset s -> Reset (rewrite rule s)
    | _ -> failwith (Format.asprintf "todo %a" Core.Pretty.pp_term target))

and rewrite_binder rule target =
  let x, target = unbind target in
  unbox (bind_var x (box_staged_spec (rewrite rule target)))

and rewrite_mbinder rule target =
  let x, target = unmbind target in
  unbox (bind_mvar x (box_staged_spec (rewrite rule target)))

open Core.Pretty
open Parsing.Parse

let%expect_test _ =
  let test rule term =
    let t0 = parse_term term in
    let t = rewrite rule t0 in
    Format.printf "%a ==> %a@." pp_term t0 pp_term t
  in
  let rule : rule = unbox (bind_mvar [||] (box_pair Mk.true_ Mk.false_)) in
  test rule "true";
  [%expect {| true ==> false |}];

  let id =
    let x = new_tvar "x" in
    Mk.fun_ (bind_mvar [| x |] (Mk.var x))
  in
  let rule : rule =
    unbox
      (bind_mvar [||]
         (box_pair
            (Mk.apply (Mk.symbol { sym_name = "f" }) (box_list [id]))
            (Mk.apply (Mk.symbol { sym_name = "g" }) (box_list [Mk.int 1]))))
  in
  test rule "f (fun x -> x)";
  [%expect {| f (fun x -> x) ==> g 1 |}]
