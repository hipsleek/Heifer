open Types
open Entail
open Pretty

(** D |--* N *)
type entail_star = state * spec

let string_of_entail_star (s, sp) =
  Format.asprintf "%s |--* %s" (string_of_state s) (string_of_spec sp)

let subst_entail_star _a _b (_state, _spec) = failwith ""

let rec staged_to_state s =
  match s with
  | [] -> (True, EmptyHeap)
  | Require (p, EmptyHeap) :: s1 ->
    let p1, h = staged_to_state s1 in
    (And (p1, p), h)
  | NormalReturn (p, h, v) :: s1 ->
    let p1, h1 = staged_to_state s1 in
    (And (And (p1, p), Atomic (EQ, Var "res", v)), SepConj (h, h1))
  | _ ->
    failwith
      (Format.asprintf "unable to convert staged to state: %s"
         (string_of_spec s))

let rec incremental_rules (pre : entail_star) (e : core_lang) :
    entail_star Res.pf =
  let open Res in
  let left, right = pre in
  match e with
  | CRead v ->
    let a = verifier_getAfreeVar () in
    let p, h = left in
    let p1 =
      check_staged_entail
        [NormalReturn (p, h, UNIT)]
        [
          Require (True, PointsTo (v, Var a));
          NormalReturn (True, PointsTo (v, Var a), Var a);
        ]
    in
    begin
      match p1 with
      | None -> Error (rule ~name:"incr-deref" "%s" v)
      | Some a ->
        let heap = staged_to_state a in
        Ok (rule ~name:"incr-deref" "%s" v, (heap, right))
    end
  | CLet (v, e1, e2) ->
    let* _pf1, r1 = incremental_rules (left, right) e1 in
    let r2 = r1 in
    let* _pf1, r1 = incremental_rules r2 e2 in
    let l1, r3 = r1 in
    Ok (rule ~name:"incr-let" "lol", (l1, Exists [v] :: r3))
  | CValue _ -> failwith "not done"
  | CIfELse (_, _, _) -> failwith "not done"
  | CFunCall (_, _) -> failwith "not done"
  | CWrite (_, _) -> failwith "not done"
  | CRef _ -> failwith "not done"
  | CAssert (_, _) -> failwith "not done"
  | CPerform (_, _) -> failwith "not done"
  | CMatch (_, _, _) -> failwith "not done"
  | CResume _ -> failwith "not done"

let%expect_test _ =
  let test name l r =
    let res = incremental_rules l r in
    Format.printf "\n--- %s\n{%s} %s %s\n\n%s\n@." name
      (string_of_entail_star l)
      (match res with
      | Ok (_pf, r1) -> Format.asprintf "{%s}" (string_of_entail_star r1)
      | Error _ -> "FAIL")
      (string_of_core_lang r)
      (match res with
      | Ok (pf, _) -> Format.asprintf "%s" (string_of_proof pf)
      | Error pf -> Format.asprintf "%s" (string_of_proof pf))
  in
  test "hello"
    ( (True, PointsTo ("a", Num 1)),
      [NormalReturn (True, PointsTo ("a", Num 1), Var "b")] )
    (CRead "a");
  [%expect
    {|
    --- hello
    {a->1 |--* Norm(a->1, b)} {a->f13*emp /\ T/\f13=1/\res=f13/\1=f13 |--* Norm(a->1, b)} !a

    │[incr-deref] a
|}]
