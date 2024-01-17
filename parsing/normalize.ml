open Hipcore
open Hiptypes
open Pretty
open Subst
open Debug

exception Norm_failure

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
  | Nil | TTrue | TFalse | UNIT | Num _ | TList _ | TTupple _ | Var _ | TApp _ | TLambda _  -> t
  | TNot a -> TNot (simplify_term a)
  | Rel (op, a, b) -> Rel (op, simplify_term a, simplify_term b)
  | Plus (Minus(t, Num n1), Num n2) -> 
    if n1 == n2 then t else if n1>= n2 then Minus(t, Num (n1-n2)) else Plus(t, Num (n1-n2))
  | Plus (a, b)  -> Plus (simplify_term a, simplify_term b)
  | TTimes (a, b)  -> TTimes (simplify_term a, simplify_term b)
  | TDiv (a, b)  -> TDiv (simplify_term a, simplify_term b)
  | Minus (a, b) -> Minus (simplify_term a, simplify_term b)
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
    | PointsTo (str, t) -> (PointsTo (str, simplify_term t), false)
    | _ -> (h, false)
  in
  to_fixed_point once h

let simplify_pure (p : pi) : pi =
  let rec once p =
    match p with
    | Not (Atomic (EQ, a, TTrue)) -> (Atomic (EQ, a, TFalse), true)
    | (Atomic (EQ, TAnd(TTrue, TTrue), TTrue)) -> (True, true)
    | (Atomic (EQ, TAnd(TFalse, TTrue), TFalse)) -> (True, true)
    | (Atomic (EQ, t1, Plus(Num n1, Num n2))) -> (Atomic (EQ, t1, Num (n1+n2)), true)

    | Atomic (EQ, a, b) when a = b -> (True, true)
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

let simplify_state (p, h) = (simplify_pure p, simplify_heap h)

let mergeState (pi1, h1) (pi2, h2) =
  let heap = simplify_heap (SepConj (h1, h2)) in
  (*print_endline (string_of_kappa (SepConj (h1, h2)) ^ " =====> ");
    print_endline (string_of_kappa heap ^ "   and    " ^ string_of_pi unification);
  *)
  (simplify_pure (And (pi1, pi2)), heap)

let rec list_of_heap h =
  match h with
  | EmptyHeap -> []
  | PointsTo (v, t) -> [(v, t)]
  | SepConj (h1, h2) -> list_of_heap h1 @ list_of_heap h2

(*
let rec deleteFromHeapList li (x, t1)  = 
  match li with 
  | [] -> failwith "deleteFromHeapList not found"
  | (y, t2)::ys -> if String.compare x y == 0 && stricTcompareTerm t1 t2 then ys
    else (y, t2):: (deleteFromHeapList ys (x, t1))


(* the accumption is h1 |- h2 ~~~~> r, and return r *)
let getheapResidue h1 h2 : kappa =  
  let listOfHeap1 = list_of_heap h1 in 
  let listOfHeap2 = list_of_heap h2 in 
  let rec helper acc li = 
    match li with 
    | [] -> acc 
    | (x, v) :: xs  -> 
      let acc' = deleteFromHeapList acc (x, v) in 
      helper acc' xs
  in 
  let temp = helper listOfHeap1 listOfHeap2  in 
  kappa_of_list temp 

*)

let rec pure_to_equalities pi =
  match pi with
  | Atomic (EQ, Var a, Var b) -> [(a, b)]
  | And (a, b) -> pure_to_equalities a @ pure_to_equalities b
  | Atomic (_, _, _)
  | True | False
  | Predicate (_, _)
  | Subsumption (_, _)
  | Or (_, _)
  | Imply (_, _)
  | Not _ ->
    []

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

let rec kappa_of_list li =
  match li with
  | [] -> EmptyHeap
  | (x, v) :: xs -> SepConj (PointsTo (x, v), kappa_of_list xs)

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
(* flag true => ens h1; req h2 *)
(* flag false => req h2; ens h1 *)
let normaliseMagicWand h1 h2 existential flag assumptions : kappa * pi =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:6
          ~title:"normaliseMagicWand"
          "%s * ?%s |- %s * ?%s\nex %s\nflag %b\nassumptions %s" 
          (string_of_kappa h1)
          (string_of_result string_of_kappa (Option.map fst r))
          (string_of_kappa h2)
          (string_of_result string_of_pi (Option.map snd r))
          (string_of_list Fun.id existential)
          flag
          (string_of_pi assumptions))
  in
  let listOfHeap1 = list_of_heap h1 in
  let listOfHeap2 = list_of_heap h2 in
  let rec helper (acc : (string * term) list * pi) li =
    let heapLi, unification = acc in
    match li with
    | [] -> acc
    | (x, v) :: xs ->
      let heapLi', unification' =
        deleteFromHeapListIfHas heapLi (x, v) existential flag assumptions
      in
      helper (heapLi', And (unification, unification')) xs
  in
  let temp, unification = helper (listOfHeap2, True) listOfHeap1 in
  (simplify_heap (kappa_of_list temp), unification)

let pure_abduction left right =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:5
          ~title:"pure_abduction"
          "%s /\\ ? |- %s\nabduced: %s\nnew left: %s\nnew right: %s" (string_of_pi left)
          (string_of_pi right)
          (string_of_result string_of_pi (Option.map (fun (a, _, _) -> a) r))
          (string_of_result string_of_pi (Option.map (fun (_, a, _) -> a) r))
          (string_of_result string_of_pi (Option.map (fun (_, _, a) -> a) r)))
  in
  (* woefully incomplete *)
  (* https://www.cs.utexas.edu/~isil/fmcad-tutorial.pdf *)
  (*
    A /\ a=b |- a <: c /\ F
    A: b <: c
    F: true
    ens a=b; req a<:c
    req b<:c; ens true
  *)
  let eqs = find_equalities#visit_pi () left in
  let subs = find_subsumptions#visit_pi () right in
  let asmp =
    subs |> List.concat_map (fun (a, f) ->
      eqs |> List.concat_map (fun (b, c) ->
          (if b = a then [Subsumption (c, f), (b, c), (a, f)] else []) @
          (if c = a then [Subsumption (b, f), (b, c), (a, f)] else [])
        ))
  in
  let abduced = List.map (fun (a, _, _) -> a) asmp |> conj in
  let left1 =
    let used = List.map (fun (_, b, _) -> b) asmp in
    (remove_equalities used)#visit_pi () left
  in
  let right1 =
    let used = List.map (fun (_, _, c) -> c) asmp in
    (remove_subsumptions used)#visit_pi () right
  in
  (* more general case? *)
  (*
    A /\ a=1 |- a=2 /\ F
    A: 1=2
    F: true
    ens a=1; req a=2
    req 1=2; ens true
  *)
  abduced, left1, right1

let normalize_step (acc : normalisedStagedSpec) (stagedSpec : stagedSpec)
    : normalisedStagedSpec =

  (*print_endline ("\nacc = " ^ string_of_normalisedStagedSpec acc);*)
  let res =
    let effectStages, (existential, req, ens) = acc in
    match stagedSpec with
    | Exists li -> (effectStages, (existential @ li, req, ens))
    | Require (p3, h3) ->
      let p2, h2 = ens in
      let magicWandHeap, unification =
        normaliseMagicWand h2 h3 existential true (And (p2, p3))
      in

      (* not only need to get the magic wand, but also need to delete the common part from h2 *)
      let h2', unification1 =
        (* TODO equalities? *)
        normaliseMagicWand h3 h2 existential false (And (p2, p3))
        (* (pure_to_equalities p2) *)
      in

      let p4, p2, p3 = pure_abduction p2 p3 in

      debug ~at:5 ~title:"biabduction" "%s * %s |- %s * %s"
        (string_of_state (unification, magicWandHeap))
        (string_of_state (p2, h2))
        (string_of_state (p3, h3))
        (string_of_state (unification1, h2'));

      let normalStage' =
        let pre = mergeState req (conj [p4; p3; unification], magicWandHeap) in
        let post = (simplify_pure (And (p2, unification1)), h2') in
        (existential, pre, post)
      in
      (effectStages, normalStage')
    | NormalReturn (pi, heap) ->
      (* pi may contain a res, so split the res out of the previous post *)
      (* if both sides contain res, remove from the left side *)
      let ens1, nex =
        if contains_res_state ens && contains_res_state (pi, heap) then
          let e, n = quantify_res_state ens in
          (e, [n])
        else (ens, [])
      in
      (* let ens1, nex = merge_state_containing_res ens (pi, heap) in *)
      (effectStages, (nex @ existential, req, mergeState ens1 (pi, heap)))
    (* effects *)
    | RaisingEff (pi, heap, ins, ret') ->
      (* the right side always contains a res. remove from the left side if present *)
      let ens1, nex =
        if contains_res_state ens then
          let e, n = quantify_res_state ens in
          (e, [n])
        else (ens, [])
      in
      (* merge_state_containing_res ens (pi, heap) in *)
      (* move current norm state "behind" this effect boundary. the return value is implicitly that of the current stage *)
      ( effectStages
        @ [
          EffHOStage {
              e_evars = nex @ existential;
              e_pre = req;
              e_post = simplify_state (mergeState ens1 (pi, heap));
              e_constr = ins;
              e_ret = ret';
              e_typ = `Eff;
            };
          ],
        freshNormStageRet ret' )
    (* higher-order functions *)
    | HigherOrder (pi, heap, ins, ret') ->
      (* let ens1, nex = merge_state_containing_res ens (pi, heap) in *)
      let ens1, nex =
        if contains_res_state ens then
          let e, n = quantify_res_state ens in
          (e, [n])
        else (ens, [])
      in
      ( effectStages
        @ [
          EffHOStage {
              e_evars = nex @ existential;
              e_pre = req;
              e_post = mergeState ens1 (pi, heap);
              e_constr = ins;
              e_ret = ret';
              e_typ = `Fn;
            };
          ],
        freshNormalStage )
    | TryCatch (pi, heap, (a, b), ret') -> 
      let ens1, nex =
        if contains_res_state ens then
          let e, n = quantify_res_state ens in
          (e, [n])
        else (ens, [])
      in
      ( effectStages
        @ [
          TryCatchStage {
              tc_evars = nex @ existential;
              tc_pre = req;
              tc_post = mergeState ens1 (pi, heap);
              tc_constr = (a, b);
              tc_ret = ret';
            };
          ],
        freshNormStageRet ret' )

  in
  debug ~at:4 ~title:"normalize_step" "%s\n+\n%s\n==>\n%s"
    (string_of_normalisedStagedSpec acc)
    (string_of_staged_spec stagedSpec)
    (string_of_normalisedStagedSpec res);
  res

(* | IndPred {name; _} -> *)
(* failwith (Format.asprintf "cannot normalise predicate %s" name) *)

let (*rec*) normalise_spec_ (acc : normalisedStagedSpec) (spec : spec) :
    normalisedStagedSpec =
  List.fold_left normalize_step acc spec
(* match spec with
     | [] -> acc
     | x :: xs ->
       (*let time_1 = Sys.time() in*)
       let acc' = normalize_step acc x in
       (*let time_2 = Sys.time() in
       let during = time_2 -. time_1 in
       (
       print_endline (string_of_stages x );
       print_endline ("[testing   Time] " ^ string_of_float ((during) *. 1000.0) ^ " ms\n"));
   *)
       normalise_spec_ acc' xs *)

let rec collect_lambdas_term (t : term) =
  match t with
  | Nil | TTrue | TFalse | UNIT | Num _ -> SSet.empty
  | TList ts | TTupple ts -> SSet.concat (List.map collect_lambdas_term ts)
  | Var _ -> SSet.empty
  | Rel (_, a, b) | Plus (a, b) | Minus (a, b) | TAnd (a, b) | TOr (a, b) | TPower(a, b) | TTimes (a, b) | TDiv (a, b)  
    ->
    SSet.union (collect_lambdas_term a) (collect_lambdas_term b)
  | TNot a -> collect_lambdas_term a
  | TApp (_, args) -> SSet.concat (List.map collect_lambdas_term args)
  | TLambda (l, _params, _sp, _body) -> SSet.singleton l
  | TCons _ -> failwith "unimplemented"

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
let remove_noncontributing_existentials :
    normalisedStagedSpec -> normalisedStagedSpec =
  (* merge equivalence classes of variables.
     probably better done using union find repr *)
  let merge_classes a1 b1 =
    let merged =
      List.fold_right
        (fun a t ->
          let added = ref false in
          let b2 =
            List.map
              (fun b ->
                if SSet.disjoint a b then b
                else (
                  added := true;
                  SSet.union a b))
              t
          in
          if !added then b2 else a :: b2)
        a1 b1
    in
    merged
  in
  let rec collect_related_vars_term t =
    match t with
    | Var v -> SSet.singleton v
    | UNIT | TTrue | TFalse | Nil | Num _ -> SSet.empty
    | Plus (a, b) | Minus (a, b) | TAnd (a, b) | TOr (a, b) | TPower(a, b) | TTimes(a, b) | TDiv(a, b)  ->
      SSet.union (collect_related_vars_term a) (collect_related_vars_term b)
    | TNot t -> collect_related_vars_term t
    | TApp (_, ts) -> SSet.concat (List.map collect_related_vars_term ts)
    | Rel (_, _, _) -> failwith (Format.asprintf "NYI rel")
    | TLambda (_, _, spec, _body) -> collect_related_vars_disj_spec spec
    | TList _ -> failwith (Format.asprintf "NYI list")
    | TTupple _ -> failwith (Format.asprintf "NYI tuple")
    | TCons _ -> failwith (Format.asprintf "NYI tcons")

  (*
    collect(a=b) = [{a, b}]
    collect(a=b /\ c<b) = [{a, b,}, {c, b}] = [{a, b, c}]
    collect(a=b /\ c=d) = [{a, b}, {c, d}]
  *)
  and collect_related_vars_pi p =
    match p with
    | True | False -> []
    | Subsumption (a, b)
    | Atomic (_, a, b) ->
      let a1 = collect_related_vars_term a in
      let b1 = collect_related_vars_term b in
      (* Format.printf "a1: %s@." (string_of_sset a1); *)
      (* Format.printf "b1: %s@." (string_of_sset b1); *)
      (* let r = merge_classes a1 b1 in *)
      let r = [SSet.union a1 b1] in
      (* Format.printf "r: %s@." (string_of_list string_of_sset r); *)
      r
    | And (a, b) | Or (a, b) | Imply (a, b) ->
      let a1 = collect_related_vars_pi a in
      let b1 = collect_related_vars_pi b in
      merge_classes a1 b1
    | Not a -> collect_related_vars_pi a
    | Predicate (_, tLi) -> 
      [List.fold_left (fun acc t -> SSet.union acc (collect_related_vars_term t)) SSet.empty tLi]
  and collect_related_vars_heap h =
    match h with
    | EmptyHeap -> []
    | PointsTo (x, y) -> [SSet.add x (collect_related_vars_term y)]
    | SepConj (a, b) ->
      let a1 = collect_related_vars_heap a in
      let b1 = collect_related_vars_heap b in
      merge_classes a1 b1
  and collect_related_vars_state (p, h) =
    let h1 = collect_related_vars_heap h in
    let p1 = collect_related_vars_pi p in
    merge_classes h1 p1
  and collect_related_vars_stage st =
    match st with
    | Require (p, h) | NormalReturn (p, h) -> collect_related_vars_state (p, h)
    | Exists _ -> []
    | HigherOrder (p, h, _constr, _ret) | RaisingEff (p, h, _constr, _ret) ->
      collect_related_vars_state (p, h)
    | TryCatch _ -> failwith "unimplemented"
  and collect_related_vars_spec s =
    SSet.concat (List.concat_map collect_related_vars_stage s)
  and collect_related_vars_disj_spec ss =
    SSet.concat (List.map collect_related_vars_spec ss)
  in
  let _handle fns ex pre post =
    let classes =
      merge_classes
        (collect_related_vars_state pre)
        (collect_related_vars_state post)
    in
    debug ~at:5 ~title:"classes" "%s" (string_of_list string_of_sset classes);
    (* heuristic: important variables (overapproximate) are:
        1. those related to universally quantified variables
        2. those which may be outputs (related to res or locations)
        3. those related to function stages *)
    let needed =
      SSet.concat
        [
          SSet.singleton "res";
          fns;
          SSet.union
            (collect_locations_vars_state pre)
            (collect_locations_vars_state post);
          SSet.diff
            (SSet.union (used_vars_state pre) (used_vars_state post))
            (SSet.of_list ex);
        ]
    in
    debug ~at:5 ~title:"needed" "%s" (string_of_sset needed);
    let do_not_contribute =
      List.filter
        (fun c -> not (SSet.exists (fun c -> SSet.mem c needed) c))
        classes
      |> SSet.concat
    in
    (* Format.printf "do_not_contribute: %s@." (string_of_sset do_not_contribute); *)
    let ex1 = List.filter (fun e -> not (SSet.mem e do_not_contribute)) ex in
    let pre1 = (remove_conjunct_with_variable_rel do_not_contribute)#visit_state () pre in
    let post1 = (remove_conjunct_with_variable_rel do_not_contribute)#visit_state () post in
    (ex1, pre1, post1)
  in
  fun (ess, norm) ->(ess, norm) (* ASK Darius*)
    (*let (ess:effectStage list) = 
      List.fold_left (fun acc a -> 
      let temp = match a with 
      | EffHOStage ele -> [ele]
      | _ -> []
      in 
      acc @ temp) [] ess 
    in 
    let fn_stages =
      List.map (fun efs -> fst efs.e_constr) ess |> SSet.of_list
    in
    let ess1 =
      List.map
        (fun efs ->
          let ex, pre, post =
            handle fn_stages efs.e_evars efs.e_pre efs.e_post
          in
          { efs with e_evars = ex; e_pre = pre; e_post = post })
        ess
    in
    let norm1 =
      let ex, pre, post = norm in
      let ex1, (p11, h1), (p21, h2) = handle fn_stages ex pre post in
      (ex1, (p11, h1), (p21, h2))
    in
    (ess1, norm1)
    *)

(* if we see [ex x; Norm(x->..., ...); ex y; Norm(y->..., ...)] and [x=y] appears somewhere, substitute y away (as y is in x's scope but not the other way around) *)
(* this does just one iteration. could do to a fixed point *)
let simplify_existential_locations sp =
  let quantifiers, _, _ =
    List.fold_left
      (fun (ex, locs, i) c ->
        match c with
        | Exists vs ->
          (* Format.printf "vs: %s %d@." (string_of_list Fun.id vs) i; *)
          (List.map (fun v -> (v, i)) vs :: ex, locs, i + 1)
        | _ -> (ex, locs, i)
        (* | Require (p, h)
           | NormalReturn (p, h)
           | HigherOrder (p, h, _, _)
           | RaisingEff (p, h, _, _) ->
             let l =
               (* used_vars_state (p, h)
                  |> SSet.filter (fun l ->
                         List.mem l (List.concat_map (List.map fst) ex)) *)
               SSet.empty
             in
             ( ex,
               (* TODO actually this is generalized to vars, not just locations *)
               (* used_locs_heap h *)
               SSet.union l locs
               (* |> SSet.filter (fun l -> SSet.mem l ex) *)
               (* |> SSet.union locs *),
               i ) *))
      ([], SSet.empty, 0) sp
  in
  let quantifiers = List.concat quantifiers in
  let eqs =
    List.concat_map
      (fun s ->
        match s with
        | Exists _ | TryCatch _ -> []
        | Require (p, _)
        | NormalReturn (p, _)
        | HigherOrder (p, _, _, _)
        | RaisingEff (p, _, _, _) ->
          pure_to_equalities p
        
          
      )

      sp
  in
  (* if there is an eq between two existential locations, keep only one *)
  List.fold_right
    (fun (a, b) sp ->
      let a1 = List.assoc_opt a quantifiers in
      let b1 = List.assoc_opt b quantifiers in
      match (a1, b1) with
      | Some ai, Some bi when a <> b ->
        let smaller = if ai <= bi then a else b in
        let larger = if ai <= bi then b else a in
        (* Format.printf "substituting %s (%d) := %s (%d)@." larger (max ai bi) smaller min ai bi; *)
        let bs = [(larger, Var smaller)] in
        instantiateSpec bs sp
      | _ -> sp)
    eqs sp


(* req false; ... ==> req false; ens false
  ens false; ... ==> ens false *)
let check_for_false (effs, norm) =
  (* returns true if the flow was truncated due to false *)
  let rec loop efs =
    match efs with
    | [] -> `Other, [], None
    | (TryCatchStage _) as e :: efs1 ->
      let r, e1, pre = loop efs1 in
      r, e :: e1, pre
    | (EffHOStage s) as e :: efs1 ->
      (match ProversEx.is_valid (fst s.e_pre) False with
      | true -> `ReqFalse, [], None
      | false ->
        (match ProversEx.is_valid (fst s.e_post) False with
            | true -> `EnsFalse, [], Some s.e_pre
            | false ->
              let r, e1, pre = loop efs1 in
              r, e :: e1, pre))
  in
  let r, effs1, pre = loop effs in
  match r, pre with
  | `ReqFalse, _ ->
    let refalse = ([], (False, EmptyHeap), (False, EmptyHeap)) in
    (effs1, refalse)
  | `EnsFalse, Some pre ->
    let refalse = ([], pre, (False, EmptyHeap)) in
    (effs1, refalse)
  | `EnsFalse, None -> failwith "invalid state"
  | `Other, _ -> (effs, norm)

let final_simplification (effs, norm) =
  let effs1 =
    List.map
      (fun efs ->
        match efs with
        | TryCatchStage tc ->
          TryCatchStage {
            tc with
            tc_pre = simplify_state tc.tc_pre;
            tc_post = simplify_state tc.tc_post;
          }
        | EffHOStage efs ->
          EffHOStage {
            efs with
            e_pre = simplify_state efs.e_pre;
            e_post = simplify_state efs.e_post;
          })
      effs
  in
  let ex, pre, post = norm in
  (effs1, (ex, simplify_state pre, simplify_state post))

(* for each existential variable, if there is only one use, remove it *)
let remove_temp_vars : normalisedStagedSpec -> normalisedStagedSpec =
  fun (eff, norm) ->
    let histo =
      count_uses_and_equalities#visit_normalisedStagedSpec () (eff, norm)
    in
    debug ~at:5 ~title:"histo" "%s\n\n%s"
      (string_of_normalisedStagedSpec (eff, norm))
      (string_of_smap
         (string_of_pair string_of_int (string_of_list string_of_term))
         histo);
    let quantified = Subst.getExistentialVar (eff, norm) |> SSet.of_list in
    let locations =
      SSet.concat
        (collect_locations_norm norm :: List.map collect_locations_eff eff)
    in
    let occurs_once =
      histo
      |> SMap.filter
        (fun k (cnt, eq) ->
          ((not (String.equal k "res")) && not (SSet.mem k locations))
          && Int.equal cnt 1 && SSet.mem k quantified &&
          (* edge case: given [ex r. res=r], we only remove r if it's not the only thing constraining res *)
          (* TODO non-equality [ex r. res > r] is not handled *)
          (if List.mem (res_v) eq then (fst (SMap.find "res" histo) > 1) else true))
      |> SMap.keys |> SSet.of_list
    in
    debug ~at:5 ~title:"occurs once" "%s" (string_of_sset occurs_once);
    (* TODO removing from existentials does not handle shadowing *)
    let norm1 = (remove_conjunct_with_variable_rel occurs_once)#visit_normalisedStagedSpec () (eff, norm) in
    (* don't remove the existential binders, only their uses. it's possible some variables which occurred once could not be removed. let a subsequent phase clean up useless existential binders *)
    norm1

(* for each existential variable, if there are two uses, substitute one into the other *)
let remove_vars_occurring_twice : normalisedStagedSpec -> normalisedStagedSpec =
  fun (eff, norm) ->
    let histo =
      count_uses_and_equalities#visit_normalisedStagedSpec () (eff, norm)
    in
    debug ~at:5 ~title:"histo" "%s\n\n%s"
      (string_of_normalisedStagedSpec (eff, norm))
      (string_of_smap
         (string_of_pair string_of_int (string_of_list string_of_term))
         histo);
    let quantified = Subst.getExistentialVar (eff, norm) |> SSet.of_list in
    let locations =
      SSet.concat
        (collect_locations_norm norm :: List.map collect_locations_eff eff)
    in
    let occurs_twice =
      SMap.filter_map
        (fun k (cnt, eqs) ->
          if
            (not (String.equal k "res"))
            && (not (SSet.mem k locations))
            && Int.equal cnt 2
            && List.length eqs >= 2
               (* f(1, v0); ens res=v0 would only have one equality, in that case we don't want to remove v0 *)
            && SSet.mem k quantified
          then Some (List.hd eqs)
          else None)
        histo
      |> SMap.bindings
    in
    debug ~at:5 ~title:"occurs twice" "%s"
      (string_of_list (string_of_pair Fun.id string_of_term) occurs_twice);
    let eff1 =
      List.map
        (fun e ->
          match e with
          | TryCatchStage tc ->
            TryCatchStage {
              tc with
              tc_pre = instantiate_state occurs_twice tc.tc_pre;
              tc_post = instantiate_state occurs_twice tc.tc_post;
            }
          | EffHOStage e ->
            EffHOStage {
              e with
              e_pre = instantiate_state occurs_twice e.e_pre;
              e_post = instantiate_state occurs_twice e.e_post;
            })
        eff
    in
    (* Format.printf "occurs_twice: %s@."
       (string_of_list (string_of_pair Fun.id string_of_term) occurs_twice); *)
    let norm1 =
      let ex, pre, post = norm in
      ( ex,
        instantiate_state occurs_twice pre,
        instantiate_state occurs_twice post )
    in
    (eff1, norm1)

let rec simplify_spec n sp2 =

  let sp3 = sp2 in

  (* we may get a formula that is not equisatisfiable *)
  (* let sp3 = sp2 |> remove_noncontributing_existentials in
     debug ~at:4 ~title:"remove existentials that don't contribute" "%s\n==>\n%s"
       (string_of_normalisedStagedSpec sp2)
       (string_of_normalisedStagedSpec sp3); *)
  (* redundant vars may appear due to fresh stages and removal of res via intermediate variables *)

  (* do this before removing unused existentials *)
  let sp4 =
    let@ _ =
      Debug.span (fun r ->
        debug ~at:4 ~title:"normalize_spec: remove temp vars" "%s\n==>\n%s"
          (string_of_normalisedStagedSpec sp3)
          (string_of_result string_of_normalisedStagedSpec r))
    in
    remove_temp_vars sp3
  in

  let sp5 =
    let@ _ =
      Debug.span (fun r ->
        debug ~at:4
            ~title:"normalize_spec: move existentials inward and remove unused"
            "%s\n==>\n%s"
            (string_of_normalisedStagedSpec sp4)
            (string_of_result string_of_normalisedStagedSpec r))
    in
    optimize_existentials sp4
  in

  let sp6 =
    let@ _ =
      Debug.span (fun r ->
        debug ~at:4 ~title:"normalize_spec: remove vars occurring twice" "%s\n==>\n%s"
          (string_of_normalisedStagedSpec sp5)
          (string_of_result string_of_normalisedStagedSpec r))
    in
    remove_vars_occurring_twice sp5
  in

  let sp7 =
    let@ _ =
      Debug.span (fun r ->
        debug ~at:4 ~title:"normalize_spec: final simplification pass" "%s\n==>\n%s"
          (string_of_normalisedStagedSpec sp6)
          (string_of_result string_of_normalisedStagedSpec r))
    in
    final_simplification sp6
  in

  if sp7 = sp2 || n < 0 then sp7 else simplify_spec (n - 1) sp2


(* the main entry point *)
let normalize_spec sp =
  (*print_endline("\nnormalize_spec:\n "^ (string_of_spec sp));*)

  let@ _ =
    Debug.span (fun r ->
        debug ~at:3 ~title:"normalize_spec" "%s\n==>\n%s" (string_of_spec sp)
          (string_of_result string_of_normalisedStagedSpec r))
  in
  let sp =
    let sp1 = sp |> simplify_existential_locations in
    debug ~at:4 ~title:"normalize_spec: remove some existential eqs"
      "%s\n==>\n%s" (string_of_spec sp) (string_of_spec sp1);
    (*print_endline ("sp1 = " ^ string_of_spec sp1);*)
    let sp2 = sp1 |> normalise_spec_ ([], freshNormalStage) in
    debug ~at:4 ~title:"normalize_spec: actually normalize" "%s\n==>\n%s"
      (string_of_spec sp1)
      (string_of_normalisedStagedSpec sp2);
    (*print_endline ((string_of_spec sp1));
    print_endline("===>\n"^ (string_of_normalisedStagedSpec sp2));*)

    sp2
  in
  let sp = simplify_spec 3 sp in

  (* let sp =
    let@ _ =
      Debug.span (fun r ->
        debug ~at:3 ~title:"normalize_spec: check for false" "%s\n==>\n%s"
          (string_of_normalisedStagedSpec sp)
          (string_of_result string_of_normalisedStagedSpec r))
    in
    check_for_false sp
  in *)
  sp


let rec effectStage2Spec (effectStages : effHOTryCatchStages list) : spec =
  match effectStages with
  | [] -> []
  | (EffHOStage eff) :: xs ->
    let p2, h2 = eff.e_post in
    (match eff.e_evars with [] -> [] | _ -> [Exists eff.e_evars])
    @ (match eff.e_pre with
      | True, EmptyHeap -> []
      | p1, h1 -> [Require (p1, h1)])
    @ [
        (match eff.e_typ with
        | `Eff -> RaisingEff (p2, h2, eff.e_constr, eff.e_ret)
        | `Fn -> HigherOrder (p2, h2, eff.e_constr, eff.e_ret));
      ]
    @ effectStage2Spec xs
  | (TryCatchStage tc):: xs -> 
    let p2, h2 = tc.tc_post in
    (match tc.tc_evars with [] -> [] | _ -> [Exists tc.tc_evars])
    @ (match tc.tc_pre with
      | True, EmptyHeap -> []
      | p1, h1 -> [Require (p1, h1)])
    @ [TryCatch (p2, h2, tc.tc_constr, tc.tc_ret)
      ]
    @ effectStage2Spec xs



let normalStage2Spec (normalStage : normalStage) : spec =
  let existiental, (p1, h1), (p2, h2) = normalStage in
  (match existiental with [] -> [] | _ -> [Exists existiental])
  @ (match (p1, h1) with True, EmptyHeap -> [] | _ -> [Require (p1, h1)])
  @
  match (p2, h2) with
  (*| (True, EmptyHeap, UNIT) -> [] *)
  | _ -> [NormalReturn (p2, h2)]


let checkTheSourceOfFalse _ = ()
  (*
  match pi' with 
  | And (pi1, pi2) -> 
    (match ProversEx.entailConstrains pi False with
    | true -> 
      checkTheSourceOfFalse pi1;
      checkTheSourceOfFalse pi2;
    | _ -> ())
  | 
  *)

let rec detectfailedAssertions (spec : spec) : spec =
  match spec with
  | [] -> []
  | Require (pi, heap) :: xs ->
    let pi' = simplify_pure pi in
    (match ProversEx.is_valid pi' False with
    | true -> 
      checkTheSourceOfFalse pi';
      (* print_endline ("\nentail False " ^ string_of_pi pi'); *)
      [Require (False, heap)]
    | _ -> Require (pi', heap) :: detectfailedAssertions xs)
  (* higher-order functions *)
  | x :: xs -> x :: detectfailedAssertions xs

let normalisedStagedSpec2Spec (normalisedStagedSpec : normalisedStagedSpec) : spec =
  let effS, normalS = normalisedStagedSpec in
  (* detectfailedAssertions *)
  (effectStage2Spec effS @ normalStage2Spec normalS)

(* spec list -> normalisedStagedSpec list *)



(* this is to delete the controdictory cases, such as Norm(true=false, _) *)
let rec existControdictionSpec (spec : spec) : bool =
  match spec with
  | [] -> false
  | Require (pi1, _)::NormalReturn (pi, _)::xs ->
    let pi' = simplify_pure (And(pi1, pi)) in
    (match ProversEx.is_valid pi' False with
    | true ->  true
    | _ -> 
      existControdictionSpec xs)
  | NormalReturn (pi, _)::xs 
  | RaisingEff (pi, _, _, _) :: xs
  | HigherOrder (pi, _, _, _) ::xs -> 
    let pi' = simplify_pure pi in
    (match ProversEx.is_valid pi' False with
    | true ->  true
    | _ -> 
      existControdictionSpec xs)

  | _ :: xs -> existControdictionSpec xs

    

let normalise_spec_list_aux2 (specLi : normalisedStagedSpec list) : spec list =
  let raw = List.map (fun a -> normalisedStagedSpec2Spec a) specLi in 
  List.filter (fun a-> not (existControdictionSpec a)) raw

let normalise_spec_list (specLi : spec list) : spec list =
  let raw = List.map
    (fun a ->
      let normalisedStagedSpec = normalize_spec a in
      (normalisedStagedSpec2Spec normalisedStagedSpec))
    specLi in 

  (* let temp = List.filter (fun a-> 
    let temp = existControdictionSpec a in 
    not (temp)) raw in  *)
  let temp = raw in
  temp 


let normalise_disj_spec_aux1 (specLi : disj_spec) : normalisedStagedSpec list =
  (*print_endline ("normalise_disj_spec_aux1");*)
  List.map (fun a -> normalize_spec a) (normalise_spec_list specLi)

let rec deleteFromStringList str (li : string list) =
  match li with
  | [] -> []
  | x :: xs ->
    if String.compare x str == 0 then xs else x :: deleteFromStringList str xs

let removeExist (specs : spec list) str : spec list =
  (*print_endline ("removeExist ===>   " ^ str );
  *)
  let aux (stage : stagedSpec) : stagedSpec =
    match stage with
    | Exists strli -> Exists (deleteFromStringList str strli)
    | _ -> stage
  in
  let helper (spec : spec) : spec = List.map (fun a -> aux a) spec in
  List.map (fun a -> helper a) specs
