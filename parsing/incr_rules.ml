open Hiptypes
open Entail
open Pretty
open Normalize

(** D |--* N *)
type entail_star = state * spec

let string_of_entail_star (s, sp) =
  Format.asprintf "%s |--* %s" (string_of_state s) (string_of_spec sp)

let subst_entail_star a b ((p, h), spec) =
  Forward_rules.
    ( (instantiatePure [(a, b)] p, instantiateHeap [(a, b)] h),
      instantiateSpec [(a, b)] spec )

type fn_spec = string list * spec

let staged_to_state s =
  (* TODO is it ok to ignore the precondition? *)
  let _es, (_vs, _pre, (p, h), v) = normalise_spec s in
  (And (p, Atomic (EQ, Var "res", v)), h)

open Res.Res

let rec incremental_rules :
    ?fn_env:(string * fn_spec) list ->
    entail_star ->
    core_lang ->
    entail_star pf =
 fun ?(fn_env = []) pre e ->
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
      | Some st ->
        let heap = staged_to_state st in
        Ok (rule ~name:"incr-deref" "%s" v, (heap, right))
    end
  | CWrite (v, e) ->
    let a = verifier_getAfreeVar () in
    let p, h = left in
    let p1 =
      check_staged_entail
        [NormalReturn (p, h, UNIT)]
        [
          Require (True, PointsTo (v, Var a));
          NormalReturn (True, PointsTo (v, e), UNIT);
        ]
    in
    begin
      match p1 with
      | None -> Error (rule ~name:"incr-assign" "%s" v)
      | Some st ->
        let heap = staged_to_state st in
        Ok (rule ~name:"incr-assign" "%s" v, (heap, right))
    end
  | CLet (v, e1, e2) ->
    let* pf1, r1 = incremental_rules ~fn_env (left, right) e1 in
    let r2 = subst_entail_star "res" (Var v) r1 in
    let* pf2, r3 = incremental_rules ~fn_env r2 e2 in
    let l1, r4 = r3 in
    Ok
      (rule ~children:[pf1; pf2] ~name:"incr-let" "%s" v, (l1, Exists [v] :: r4))
  | CValue v ->
    let p, h = left in
    Ok
      ( rule ~name:"incr-value" "%s" (string_of_term v),
        ((And (p, Atomic (EQ, Var "res", v)), h), right) )
  | CRef v ->
    let p, h = left in
    Ok
      ( rule ~name:"incr-ref" "%s" (string_of_term v),
        ((p, SepConj (h, PointsTo ("res", v))), right) )
  | CAssert (p, h) ->
    (* TODO vars *)
    let res = Heap.entails ([], left) ([], (p, h)) in
    begin
      match res with
      | Ok (pf, _) ->
        Ok
          ( rule ~children:[pf] ~name:"incr-assert" "%s" (string_of_state (p, h)),
            pre )
      | Error pf ->
        Error
          (rule ~children:[pf] ~name:"incr-assert" "%s"
             (string_of_state (p, h)))
    end
  | CFunCall (fn, args) ->
    let p, h = left in
    let d2 =
      match List.assoc_opt fn fn_env with
      | Some (_params, fnspec) ->
        staged_to_state (NormalReturn (p, h, UNIT) :: fnspec)
      | None ->
        staged_to_state
          [
            NormalReturn (p, h, UNIT);
            HigherOrder (True, EmptyHeap, (fn, args), UNIT);
          ]
    in
    Ok (rule ~name:"incr-call" "%s" fn, (d2, right))
  | CIfELse (c, t, e) ->
    let p, h = left in
    (* TODO bool term? *)
    let* pf1, t1 =
      incremental_rules ~fn_env ((And (p, Atomic (EQ, c, Num 1)), h), right) t
    in
    let* pf2, e1 =
      incremental_rules ~fn_env ((And (p, Atomic (EQ, c, Num 0)), h), right) e
    in
    (* TODO combine disjunctively *)
    let disj a _b = a in
    Ok (rule ~children:[pf1; pf2] ~name:"incr-if" "", disj t1 e1)
  (* TODO lambda *)
  | CPerform (_, _) -> failwith "not done, effect-related"
  | CMatch (_, _, _, _) -> failwith "not done, effect-related"
  | CResume _ -> failwith "not done, effect-related"

let%expect_test _ =
  verifier_counter_reset ();
  let test ?fn_env name l r =
    let res = incremental_rules ?fn_env l r in
    Format.printf "--- %s\n{%s}\n%s\n%s\n\n%s@." name (string_of_entail_star l)
      (string_of_core_lang r)
      (match res with
      | Ok (_pf, r1) -> Format.asprintf "{%s}" (string_of_entail_star r1)
      | Error _ -> "{/}")
      (match res with
      | Ok (pf, _) -> Format.asprintf "%s" (string_of_proof pf)
      | Error pf -> Format.asprintf "%s" (string_of_proof pf))
  in
  test "ref"
    ( (True, PointsTo ("a", Num 1)),
      [NormalReturn (True, PointsTo ("a", Num 1), Var "b")] )
    (CRead "a");
  test "let"
    ( (True, PointsTo ("a", Num 1)),
      [NormalReturn (True, PointsTo ("a", Num 1), Var "b")] )
    (CLet ("x", CValue (Num 1), CValue (Var "x")));
  test
    ~fn_env:
      [
        ( "plus",
          (["a"; "b"], [NormalReturn (True, EmptyHeap, Plus (Var "a", Var "b"))])
        );
      ]
    "hello"
    ( (True, EmptyHeap),
      [
        Require (True, PointsTo ("p", Var "a"));
        NormalReturn (True, PointsTo ("a", Plus (Var "a", Num 1)), UNIT);
      ] )
    (CLet
       ( "n",
         CRead "p",
         CLet ("m", CFunCall ("plus", [Var "n"; Num 1]), CWrite ("p", Var "m"))
       ));
  [%expect
    {|
    --- ref
    {a->1 |--* Norm(a->1, b)}
    !a
    {a->_f0 /\ _f0=1/\res=_f0 |--* Norm(a->1, b)}

    │[incr-deref] a

    --- let
    {a->1 |--* Norm(a->1, b)}
    let x = 1 in
    x
    {a->1 /\ T/\x=1/\res=x |--* ex x; Norm(a->1, b)}

    │[incr-let] x
    │├── [incr-value] 1
    │└── [incr-value] x

    --- hello
    {emp |--* req p->a; Norm(a->a+1, ())}
    let n = !p in
    let m = plus n 1 in
    p := m
    {p->m /\ n=_f3/\m=a+b/\_f7=_f3/\res=() |--* ex n; ex m; req p->a; Norm(a->a+1, ())}

    │[incr-let] n
    │├── [incr-deref] p
    │└── [incr-let] m
    │    ├── [incr-call] plus
    │    └── [incr-assign] p
|}]
