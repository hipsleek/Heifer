open Hipcore
open Hiptypes
open Debug
open Variables


(*
let rec existStr str li =
  match li with
  | [] -> false
  | x :: xs -> if String.compare x str == 0 then true else existStr str xs

let rec to_fixed_point f spec =
  let spec, changed = f spec in
  if not changed then spec else to_fixed_point f spec

let rec to_fixed_point_ptr_eq f spec =
  let spec1 = f spec in
  if spec == spec1 then spec else to_fixed_point_ptr_eq f spec

let rec simplify_term t : term  =
  match t with
  | Nil | TTrue | TFalse | UNIT | Num _ | TList _ | TTupple _ | Var _ | TApp _ | TLambda _ | TStr _ -> t
  | TNot a -> TNot (simplify_term a)
  | Rel (op, a, b) -> Rel (op, simplify_term a, simplify_term b)
  | SConcat (TStr a, TStr b) ->  TStr (a ^ b)
  | SConcat _ ->  t
  | Plus (Minus(t, Num n1), Num n2) ->
    if n1 == n2 then t
    else if n1>= n2 then Minus(t, Num (n1-n2))
    else Plus(t, Num (n2-n1))


  | Minus (Minus(t, Num n1), Num n2) -> Minus(t, Num (n1+n2))

  | Plus (Plus(a, Num n1), Minus(b, Num n2))  -> Plus(Plus(a, b), Num (n1-n2))

  | Plus (Plus(a, Num n1), Num n2)  -> Plus(a, Num (n1+n2))

  | Plus (a, Num n)  -> if n < 0 then Minus (a, Num (-1 * n)) else t


  | Plus (Plus(Plus(a, TPower(Num 2, Var v1)), Num(n1)), TPower(Num 2, Var v2))  ->
    if String.compare v1 v2 == 0 then Plus (Plus(a, TPower(Num 2, Plus(Var v1, Num 1))), Num(n1) )
    else t

  | Plus (a, b)  ->
    let a' = simplify_term a in
    let b' = simplify_term b in
    (*print_endline (string_of_term t);
    print_endline ("===>" ^ string_of_term a' ^ "+" ^ string_of_term b');
    *)
    (match a', b' with
    | Num n1, Num n2 -> Num(n1 + n2)
    | _, _ -> Plus (a', b')
    )

  | TTimes (a, b)  ->
    let a' = simplify_term a in
    let b' = simplify_term b in
    (match a', b' with
    | Num n1, Num n2 -> Num(n1*n2)
    | _, _ -> TTimes (a', b')
    )

  | TDiv (a, b)  ->
    let a' = simplify_term a in
    let b' = simplify_term b in
    (match a', b' with
    | Num n1, Num n2 -> Num(n1/n2)
    | _, _ -> TDiv (a', b')
    )

  | Minus (a, b) ->
    let a' = simplify_term a in
    let b' = simplify_term b in
    (match a', b' with
    | Num n1, Num n2 -> Num(n1 - n2)
    | _, _ -> Minus (a', b')
    )


  | TAnd (a, b) -> TAnd (simplify_term a, simplify_term b)
  | TOr (a, b) -> TOr (simplify_term a, simplify_term b)
  | TPower(a, b) -> TPower (simplify_term a, simplify_term b)
  | TCons(a, b) -> TCons (simplify_term a, simplify_term b)

let rec simplify_heap h : kappa =
  let once h =
    match h with
    (*
  | SepConj (PointsTo (s1, t1), PointsTo (s2, t2)) ->
    if String.compare s1 s2 == 0 then (PointsTo (s1, t1), Atomic(EQ, t1, t2))
    else (h, True)
  *)
    | SepConj (EmptyHeap, h1) -> (simplify_heap h1, true)
    | SepConj (h1, EmptyHeap) -> (simplify_heap h1, true)
    | PointsTo (str, t) ->
      (*print_endline (string_of_term t); *)
      (PointsTo (str, simplify_term t), false)
    | _ -> (h, false)
  in
  to_fixed_point once h

let compareTerms (t1:term) (t2:term) : bool =
  let str1= string_of_term t1 in
  let str2= string_of_term t2 in
  if String.compare str1 str2 == 0 then true else false


let simplify_pure (p : pi) : pi =
  let rec once p =
    match p with
    | Not (Atomic (EQ, a, TTrue)) -> (Atomic (EQ, a, TFalse), true)
    | (Atomic (EQ, t1, t2 )) ->
      let t1 = simplify_term t1 in
      let t2 = simplify_term t2 in
      (match t1, t2 with
      | Var "res", Var "res" -> (True, true)
      | TFalse, TFalse -> (True, true)
      | TTrue, TTrue -> (True, true)
      | Num n1, Num n2 ->
        if n1==n2 then (True, true)
        else (p, true)

      | TAnd(TTrue, TTrue), TTrue -> (True, true)
      | TAnd(TFalse, TTrue), TFalse -> (True, true)
      | t1, Plus(Num n1, Num n2) -> (Atomic (EQ, t1, Num (n1+n2)), true)
      | _, _ ->
        if compareTerms t1 t2 then
        (
        (True, true))
        else
        (
        (Atomic (EQ, t1, t2 )), false )

      )


    | True | False | Atomic _ | Predicate _ | Subsumption _ -> (p, false)
    | And (True, a) | And (a, True) -> (a, true)
    | And (a, b) ->
      let a1, c1 = once a in
      let b1, c2 = once b in
      if c1 || c2 then (And (a1, b1), true) else (p, false)
    | Or (False, a) | Or (a, False) -> (a, true)
    | Or (a, b) ->
      let a1, c1 = once a in
      let b1, c2 = once b in
      if c1 || c2 then (Or (a1, b1), true) else (p, false)
    | Imply (a, b) ->
      let a1, c1 = once a in
      let b1, c2 = once b in
      if c1 || c2 then (Imply (a1, b1), true) else (p, false)
    | Not a ->
      let a1, c1 = once a in
      if c1 then (Not a1, true) else (p, false)
  in
  let r = to_fixed_point once p in
  (* (match (p, r) with
  | True, True -> ()
  | _ -> *)
    debug ~at:5 ~title:"simplify_pure" "%s\n==>\n%s" (string_of_pi p)
      (string_of_pi r)
      (* ) *)
      ;
  r

let rec lookforEqualityinPure (str : string) (p:pi) : term option =
  match p with
  | Atomic (EQ, Var v, t) ->
    if String.compare v str == 0 then Some t
    else None
  | True
  | False
  | Imply  _
  | Not   _
  | Predicate _
  | Subsumption _
  | Or _
  | Atomic _ -> None
  | And (p1, p2) ->
    (match lookforEqualityinPure str p1 with
    | Some t -> Some t
    | None -> lookforEqualityinPure str p2
    )

let rec accumulateTheSum (p:pi) (h:kappa) : kappa =
  match h with
  | EmptyHeap -> h
  | PointsTo (pointer, term) ->
    let term' = accumulateTheSumTerm p term in
    PointsTo (pointer, term')
  | SepConj (h1, h2) -> SepConj (accumulateTheSum p h1, accumulateTheSum p h2)

let simplify_state (p, h) =
  let (p, h) = (simplify_pure p, simplify_heap h) in
  let h' = accumulateTheSum p h in
  (p, h')

let mergeState (pi1, h1) (pi2, h2) =
  let heap = simplify_heap (SepConj (h1, h2)) in
  (*print_endline (string_of_kappa (SepConj (h1, h2)) ^ " =====> ");
    print_endline (string_of_kappa heap ^ "   and    " ^ string_of_pi unification);
  *)
  (simplify_pure (And (pi1, pi2)), heap)

let pure_to_eq_state (p, _) = pure_to_equalities p

(** check if x=y is not invalid (i.e. sat) under the given assumptions *)
let may_be_equal _assumptions _x _y =
  (* let@ _ =
       Debug.span (fun r ->
           debug ~at:4 ~title:"may be equal" "%s => %s = %s\n%s"
             (string_of_pi assumptions) (string_of_term x) (string_of_term y)
             (string_of_result string_of_bool r))
     in
     let tenv =
       Infer_types.infer_types_pi (create_abs_env ())
         (And (assumptions, Atomic (EQ, x, y)))
       |> Infer_types.concrete_type_env
     in
     let right = Atomic (EQ, x, y) in
     (* let eq = Provers.entails_exists tenv assumptions [] right in *)
     let eq = Provers.askZ3 tenv (Imply (assumptions, right)) in
     eq *)
  (* proving at this point is not effective as we may not be able to prove unsat, but later the constraints may be violated, resulting in false anyway. returning true here is just the worst case version of that *)
  true

(* (x, t1) -* (y, t2), where li is a heap containing y *)
(* flag true => add to precondition *)
(* flag false => add to postcondition *)
let rec deleteFromHeapListIfHas li (x, t1) existential flag assumptions :
    (string * term) list * pi =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:6
          ~title:"deleteFromHeapListIfHas"
          "(%s, %s) -* %s = %s\nex %s\nflag %b\nassumptions %s"
          x (string_of_term t1)
          (string_of_list (string_of_pair Fun.id string_of_term) li)
          (string_of_result (string_of_pair (string_of_list (string_of_pair Fun.id string_of_term)) string_of_pi) r)
          (string_of_list Fun.id existential)
          flag
          (string_of_pi assumptions))
  in
  let res =
    match li with
    | [] -> ([], True)
    | (y, t2) :: ys ->
      let same_loc =
        let exists_eq =
          List.mem x existential && List.mem y existential
          && may_be_equal True (Var x) (Var y)
        in
        String.equal x y || exists_eq
      in
      if same_loc then
        (* toggles whether or not z3 is used for equality checks. not using z3 is about 3x faster but causes unsoundness due to normalization not producing [req F]s if misses the fact that two values are not equal *)
        let fast_equality = false in
        begin
          match fast_equality with
          | true ->
            if stricTcompareTerm t2 (Var "_") then (ys, True)
            else (
              (* TODO these cases could be organised better... a few classes:
                 - one side is a variable
                 - both sides are variables
                 - both sides are obviously (un)equal
                 - both sides are not obviously equal (requiring z3 to check)
              *)
              match (t1, t2) with
              (* x-> z -* x-> 11   ~~~>  (emp, z=11) *)
              | Var t2Str, (Num _ | UNIT | TTrue | TFalse | Nil) ->
                if String.compare t2Str "_" == 0 then (ys, True)
                else (ys, Atomic (EQ, t1, t2))
              (* x->11 -* x-> z   ~~~>   (emp, true) *)
              | (Num _ | UNIT | TTrue | TFalse | Nil), Var t2Str ->
                if existStr t2Str existential then (ys, True)
                else (ys, Atomic (EQ, t1, t2))
              | Num a, Num b -> (ys, if a = b then True else raise Norm_failure)
              | UNIT, UNIT | TTrue, TTrue | TFalse, TFalse | Nil, Nil ->
                (ys, True)
              | _, _ ->
                if stricTcompareTerm t1 t2 || stricTcompareTerm t1 (Var "_")
                then (ys, True)
                else if flag then
                  (* ex a. x->a |- ex b. req x->b *)
                  (* a=b should be added in the result's postcondition.
                     this should be req (emp, true); ens emp, a=b *)
                  (ys, True)
                else (ys, Atomic (EQ, t1, t2))
                  (* | _, _ -> if flag then (ys, Atomic (EQ, t1, t2)) else (ys, True) *))
          | false ->
            (* handling the simple cases like this speeds things up by about 27% *)
            (match (t1, t2) with
            | Num a, Num b -> (ys, if a = b then True else raise Norm_failure)
            | Var a, Var b when a = b -> (ys, True)
            | UNIT, UNIT | TTrue, TTrue | TFalse, TFalse | Nil, Nil -> (ys, True)
            | _, _ ->
              ( ys,
                if may_be_equal assumptions t1 t2 then Atomic (EQ, t1, t2)
                else raise Norm_failure ))
        end
      else
        let res, uni =
          deleteFromHeapListIfHas ys (x, t1) existential flag assumptions
        in
        ((y, t2) :: res, uni)
  in
  let () =
    let sof = string_of_list (string_of_pair Fun.id string_of_term) in
    debug ~at:5 ~title:"delete from heap list" "%s -* %s = %s\nex %s"
      (string_of_pair Fun.id string_of_term (x, t1))
      (sof li)
      (string_of_pair sof string_of_pi res)
      (string_of_list Fun.id existential)
  in
  res

(* h1 * h |- h2, returns h and unificiation
   x -> 3 |- x -> z   -> (emp, true )
   x -> z |- x -> 3   -> (emp, z = 3)
*)

(* | IndPred {name; _} -> *)
(* failwith (Format.asprintf "cannot normalise predicate %s" name) *)

let rec collect_lambdas_term (t : term) =
  match t with
  | Nil | TTrue | TFalse | UNIT | Num _ -> SSet.empty
  | TList ts | TTupple ts -> SSet.concat (List.map collect_lambdas_term ts)
  | Var _ -> SSet.empty
  | Rel (_, a, b) | Plus (a, b) | Minus (a, b) | TAnd (a, b) | TOr (a, b) | TPower(a, b) | TTimes (a, b) | TDiv (a, b) | SConcat (a, b)
    ->
    SSet.union (collect_lambdas_term a) (collect_lambdas_term b)
  | TNot a -> collect_lambdas_term a
  | TApp (_, args) -> SSet.concat (List.map collect_lambdas_term args)
  | TLambda (l, _params, _sp, _body) -> SSet.singleton l
  | TCons _ -> failwith "unimplemented"
  | TStr _ -> failwith "unimplemented"


let rec collect_lambdas_pi (p : pi) =
  match p with
  | True | False -> SSet.empty
  | Subsumption (a, b)
  | Atomic (_, a, b) ->
    SSet.union (collect_lambdas_term a) (collect_lambdas_term b)
  | And (a, b) | Or (a, b) | Imply (a, b) ->
    SSet.union (collect_lambdas_pi a) (collect_lambdas_pi b)
  | Not a -> collect_lambdas_pi a
  | Predicate (_, t) ->
    List.fold_left (fun acc a -> SSet.union acc (collect_lambdas_term a)) SSet.empty t



let rec collect_lambdas_heap (h : kappa) =
  match h with
  | EmptyHeap -> SSet.empty
  | PointsTo (_, t) -> collect_lambdas_term t
  | SepConj (a, b) ->
    SSet.union (collect_lambdas_heap a) (collect_lambdas_heap b)

let collect_lambdas_state (p, h) =
  SSet.union (collect_lambdas_pi p) (collect_lambdas_heap h)

let collect_lambdas_eff eff =
  match eff with
  | EffHOStage eff ->
  SSet.concat
    [
      collect_lambdas_state eff.e_pre;
      collect_lambdas_state eff.e_post;
      SSet.concat (List.map collect_lambdas_term (snd eff.e_constr));
      collect_lambdas_term eff.e_ret;
    ]
  | _ -> SSet.empty

let collect_lambdas_norm (_vs, pre, post) =
  SSet.concat [collect_lambdas_state pre; collect_lambdas_state post]

let collect_lambdas (sp : normalisedStagedSpec) =
  let effs, norm = sp in
  SSet.concat (collect_lambdas_norm norm :: List.map collect_lambdas_eff effs)

let rec collect_locations_heap (h : kappa) =
  match h with
  | EmptyHeap -> SSet.empty
  | PointsTo (v, Var x) -> SSet.of_list [v; x]
  | PointsTo (v, _) -> SSet.singleton v
  | SepConj (a, b) ->
    SSet.union (collect_locations_heap a) (collect_locations_heap b)

let collect_locations_vars_state (_, h) = collect_locations_heap h

let collect_locations_eff (eff:effHOTryCatchStages) =
  match eff with
  | EffHOStage eff  ->
  SSet.concat
    [
      collect_locations_vars_state eff.e_pre;
      collect_locations_vars_state eff.e_post;
    ]
  | _ -> SSet.empty

let collect_locations_norm (_vs, pre, post) =
  SSet.concat
    [collect_locations_vars_state pre; collect_locations_vars_state post]

let collect_locations (sp : normalisedStagedSpec) =
  let effs, norm = sp in
  SSet.concat
    (collect_locations_norm norm :: List.map collect_locations_eff effs)

(** this moves existentials inward and removes unused ones *)
let optimize_existentials : normalisedStagedSpec -> normalisedStagedSpec =
 fun (ess, norm) ->
  let@ _ =
    Debug.span (fun r ->
        debug ~at:4
          ~title:"optimize_existentials result"
          "%s\n==>\n%s" (string_of_normalisedStagedSpec (ess, norm))
          (string_of_result string_of_normalisedStagedSpec r))
  in
  let rec loop already_used unused acc es =
    debug ~at:4 ~title:"optimize_existentials loop"
    "already used: %s\nunused: %s\nacc: %s\nes: %s"
       (string_of_sset already_used)
       (string_of_sset unused)
       (string_of_list string_of_effHOTryCatchStages acc)
       (string_of_list string_of_effHOTryCatchStages es);
    match es with
    | [] -> (unused, List.rev acc)
    | e :: rest ->
      let available_to_use =
        SSet.diff (SSet.union (SSet.of_list (get_existentials_eff e)) unused) already_used
      in
      let needed = SSet.diff (used_vars_eff e) already_used in
      let used_ex, unused_ex =
        SSet.partition (fun v -> SSet.mem v needed) available_to_use
      in
      loop
        (SSet.union already_used used_ex)
        unused_ex
        (set_existentials_eff e (SSet.elements used_ex) :: acc)
        rest
  in
  let unused, es1 = loop SSet.empty SSet.empty [] ess in
  let norm1 =
    let used = used_vars_norm norm in
    let evars, h, p = norm in
    let may_be_used = SSet.union (SSet.of_list evars) unused in
    (* unused ones are dropped *)
    let used_ex, _unused_ex =
      SSet.partition (fun v -> SSet.mem v used) may_be_used
    in
    (SSet.elements used_ex, h, p)
  in
  (es1, norm1)

let remove_conjunct_with_variable_rel included =
  object
    inherit [_] map_normalised
    method! visit_Atomic _ op a b =
      match a, b with
      | Var v, _ when SSet.mem v included -> True
      | _, Var v when SSet.mem v included -> True
      | _ ->
        Atomic (op, a, b)
  end

let remove_existentials vs =
  object
    inherit [_] map_normalised
    method! visit_Exists _ xs = Exists (List.filter (fun x -> not (SSet.mem x vs)) xs)
  end

(** remove existentials which don't contribute to the result, e.g.
  ex v1 v2. ens v1=v2; ens res=2
  ==>
  ens res=2
*)
*)

open Rewriting
open Rules
open Syntax

let norm_bind_val = Staged.dynamic_rule
  (Bind (Binder.uvar "x", NormalReturn (eq res_var (Term.uvar "r"), emp), Staged.uvar "f"))
  (fun sub ->
    let x = sub "x" |> Binder.of_uterm in
    let r = sub "r" |> Term.of_uterm in
    let f = sub "f" |> Staged.of_uterm in
    Subst.subst_free_vars [(x, r)] f)

let norm_bind_disj = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Disjunction (Staged.uvar "f1", Staged.uvar "f2"), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let f1 = Staged.of_uterm (sub "f1") in
    let f2 = Staged.of_uterm (sub "f2") in
    let fk = Staged.of_uterm (sub "fk") in
    Disjunction (Bind (x, f1, fk), Bind (x, f2, fk)))

(* we can push req outside of bind *)
let norm_bind_req = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Sequence (Require (Pure.uvar "p", Heap.uvar "h"), Staged.uvar "f"), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f = Staged.of_uterm (sub "f") in
    let fk = Staged.of_uterm (sub "fk") in
    Sequence (Require (p, h), Bind (x, f, fk)))

(* bind (seq (ens Q) f) fk `entails` seq (ens Q) (bind f fk) *)
(* we can push ens outside of bind; if the result of ens is not used *)
let norm_bind_seq_ens = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Sequence (NormalReturn (Pure.uvar "p", Heap.uvar "h"), Staged.uvar "f"), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f = Staged.of_uterm (sub "f") in
    let fk = Staged.of_uterm (sub "fk") in
    Sequence (NormalReturn (p, h), Bind (x, f, fk)))

let normalization_rules = [
  norm_bind_val;
  norm_bind_disj;
  norm_bind_req;
  norm_bind_seq_ens;
]

(* the main entry point *)
let normalize_spec (spec : staged_spec) : staged_spec =
  let@ _ = Globals.Timing.(time norm) in
  let@ _ =
    span (fun r -> debug
      ~at:1
      ~title:"normalize_spec"
      "%s\n==>\n%s"
      (Pretty.string_of_staged_spec spec)
      (string_of_result Pretty.string_of_staged_spec r))
  in
  let spec = Staged.of_uterm (autorewrite normalization_rules (Staged spec)) in
  spec

(* inline tests *)
let%expect_test "rules" =
  let test rule input =
    let input = Staged input in
    let output = rewrite_all rule input in
    let output = Staged.of_uterm output in
    Format.printf "%s@." (Pretty.string_of_staged_spec output)
  in
  let _ =
    let f1 = ens ~p:(eq res_var (num 1)) () in
    let f2 = ens ~p:(eq res_var (num 2)) () in
    let fk = ens ~p:(eq res_var (plus (var "x") (num 1))) () in
    let input = bind "x" (disj [f1; f2]) fk in
    (* let output = disj [bind "x" f1 fk; bind "x" f2 fk] in *)
    test norm_bind_disj input;
    [%expect
      {| (let x = (ens res=1) in (ens res=(x + 1))) \/ (let x = (ens res=2) in (ens res=(x + 1))) |}]
  in
  let _ =
    let f = ens ~p:(eq res_var (num 1)) () in
    let fk = ens ~p:(eq res_var (plus (var "x") (num 1))) () in
    let input = bind "x" (seq [f; f]) fk in
    test norm_bind_seq_ens input;
    [%expect
      {| ens res=1; let x = (ens res=1) in (ens res=(x + 1)) |}]
  in
  ()
