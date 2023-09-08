open Hiptypes
open Pretty

exception Norm_failure

let rec findbinding str vb_li =
  match vb_li with
  | [] -> Var str
  | (name, v) :: xs ->
    if String.compare name str == 0 then v else findbinding str xs

let rec instantiateTerms (bindings : (string * core_value) list) (t : term) :
    term =
  match t with
  | Nil | Num _ | UNIT | TTrue | TFalse -> t
  | Var str ->
    let binding = findbinding str bindings in
    (* Format.printf "replacing %s with %s under %s@." str (string_of_term binding) (string_of_list (string_of_pair Fun.id string_of_term) bindings); *)
    binding
  | TList tLi -> TList (List.map (fun t1 -> instantiateTerms bindings t1) tLi)
  | TTupple tLi -> TList (List.map (fun t1 -> instantiateTerms bindings t1) tLi)
  | TNot t1 -> TNot (instantiateTerms bindings t1)
  | TAnd (t1, t2) ->
    TAnd (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | TOr (t1, t2) ->
    TOr (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | Plus (t1, t2) ->
    Plus (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | Rel (bop, t1, t2) ->
    Rel (bop, instantiateTerms bindings t1, instantiateTerms bindings t2)
  | Minus (t1, t2) ->
    Minus (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | TApp (t1, t2) -> TApp (t1, List.map (instantiateTerms bindings) t2)
  | TLambda n -> TLambda n

let rec instantiatePure (bindings : (string * core_value) list) (pi : pi) : pi =
  match pi with
  | True | False -> pi
  | Atomic (bop, t1, t2) ->
    Atomic (bop, instantiateTerms bindings t1, instantiateTerms bindings t2)
  | And (p1, p2) ->
    And (instantiatePure bindings p1, instantiatePure bindings p2)
  | Or (p1, p2) -> Or (instantiatePure bindings p1, instantiatePure bindings p2)
  | Imply (p1, p2) ->
    Imply (instantiatePure bindings p1, instantiatePure bindings p2)
  | Not p1 -> Not (instantiatePure bindings p1)
  | Predicate (str, t1) -> Predicate (str, instantiateTerms bindings t1)

let rec instantiateHeap (bindings : (string * core_value) list) (kappa : kappa)
    : kappa =
  match kappa with
  | EmptyHeap -> kappa
  | PointsTo (str, t1) ->
    let binding = findbinding str bindings in
    let newName = match binding with Var str1 -> str1 | _ -> str in
    PointsTo (newName, instantiateTerms bindings t1)
  | SepConj (k1, k2) ->
    SepConj (instantiateHeap bindings k1, instantiateHeap bindings k2)

let instantiate_state bindings (p, h) =
  (instantiatePure bindings p, instantiateHeap bindings h)

let instantiateStages (bindings : (string * core_value) list)
    (stagedSpec : stagedSpec) : stagedSpec =
  match stagedSpec with
  | Exists _ -> stagedSpec
  | Require (pi, kappa) ->
    Require (instantiatePure bindings pi, instantiateHeap bindings kappa)
  (* higher-order functions *)
  | NormalReturn (pi, kappa, ret) ->
    NormalReturn
      ( instantiatePure bindings pi,
        instantiateHeap bindings kappa,
        instantiateTerms bindings ret )
  | HigherOrder (pi, kappa, (str, basic_t_list), ret) ->
    let constr =
      match List.assoc_opt str bindings with Some (Var s) -> s | _ -> str
    in
    HigherOrder
      ( instantiatePure bindings pi,
        instantiateHeap bindings kappa,
        (constr, List.map (fun bt -> instantiateTerms bindings bt) basic_t_list),
        instantiateTerms bindings ret )
  (* effects *)
  | RaisingEff (pi, kappa, (label, basic_t_list), ret) ->
    RaisingEff
      ( instantiatePure bindings pi,
        instantiateHeap bindings kappa,
        (label, List.map (fun bt -> instantiateTerms bindings bt) basic_t_list),
        instantiateTerms bindings ret )
(* | Pred {name; args}  ->  *)
(* Pred {name; args = List.map (instantiateTerms bindings) args} *)

let instantiateSpec (bindings : (string * core_value) list) (sepc : spec) : spec
    =
  List.map (fun a -> instantiateStages bindings a) sepc

let instantiateSpecList (bindings : (string * core_value) list)
    (sepcs : disj_spec) : disj_spec =
  List.map (fun a -> instantiateSpec bindings a) sepcs

let rec existStr str li =
  match li with
  | [] -> false
  | x :: xs -> if String.compare x str == 0 then true else existStr str xs

let rec normaliseHeap h : kappa =
  match h with
  (*
  | SepConj (PointsTo (s1, t1), PointsTo (s2, t2)) -> 
    if String.compare s1 s2 == 0 then (PointsTo (s1, t1), Atomic(EQ, t1, t2))
    else (h, True)
  *)
  | SepConj (EmptyHeap, h1) -> normaliseHeap h1
  | SepConj (h1, EmptyHeap) -> normaliseHeap h1
  | _ -> h

let mergeState (pi1, h1) (pi2, h2) =
  let heap = normaliseHeap (SepConj (h1, h2)) in
  (*print_endline (string_of_kappa (SepConj (h1, h2)) ^ " =====> ");
    print_endline (string_of_kappa heap ^ "   and    " ^ string_of_pi unification);
  *)
  (ProversEx.normalize_pure (And (pi1, pi2)), heap)

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
  | Or (_, _)
  | Imply (_, _)
  | Not _ ->
    []

let pure_to_eq_state (p, _) = pure_to_equalities p

(** check if x=y is not invalid (i.e. sat) under the given assumptions *)
let may_be_equal ex assumptions x y =
  let tenv =
    Infer_types.infer_types_pi (create_abs_env ())
      (And (assumptions, Atomic (EQ, x, y)))
    |> Infer_types.concrete_type_env
  in
  let right = Atomic (EQ, x, y) in
  let eq = Provers.entails_exists tenv assumptions ex right in
  debug ~at:3 ~title:"may be equal" "%s => ex %s. %s = %s\n%b"
    (string_of_pi assumptions) (string_of_list Fun.id ex) (string_of_term x)
    (string_of_term y) eq;
  eq

let rec kappa_of_list li =
  match li with
  | [] -> EmptyHeap
  | (x, v) :: xs -> SepConj (PointsTo (x, v), kappa_of_list xs)

(* (x, t1) -* (y, t2), where li is a heap containing y *)
(* flag true => add to precondition *)
(* flag false => add to postcondition *)
let rec deleteFromHeapListIfHas li (x, t1) existential flag assumptions :
    (string * term) list * pi =
  let res =
    match li with
    | [] -> ([], True)
    | (y, t2) :: ys ->
      let same_loc =
        let exists_eq =
          List.mem x existential && List.mem y existential
          && may_be_equal existential True (Var x) (Var y)
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
                if may_be_equal existential assumptions t1 t2 then
                  Atomic (EQ, t1, t2)
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
    debug ~at:3 ~title:"delete from heap list" "%s -* %s = %s\nex %s"
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
  (normaliseHeap (kappa_of_list temp), unification)

let normalise_stagedSpec (acc : normalisedStagedSpec) (stagedSpec : stagedSpec)
    : normalisedStagedSpec =
  let res =
    let effectStages, normalStage = acc in
    let existential, req, ens, ret = normalStage in
    match stagedSpec with
    | Exists li -> (effectStages, (existential @ li, req, ens, ret))
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

      debug ~at:3 ~title:"biabduction" "%s * %s |- %s * %s"
        (string_of_state (unification, magicWandHeap))
        (string_of_state ens)
        (string_of_state (p3, h3))
        (string_of_state (unification1, h2'));

      let normalStage' =
        let pre = mergeState req (And (p3, unification), magicWandHeap) in
        let post = (ProversEx.normalize_pure (And (p2, unification1)), h2') in
        (existential, pre, post, ret)
      in
      (effectStages, normalStage')
    | NormalReturn (pi, heap, ret') ->
      (effectStages, (existential, req, mergeState ens (pi, heap), ret'))
    (* effects *)
    | RaisingEff (pi, heap, ins, ret') ->
      (* move current norm state "behind" this effect boundary. the return value is implicitly that of the current stage *)
      ( effectStages
        @ [
            {
              e_evars = existential;
              e_pre = req;
              e_post = mergeState ens (pi, heap);
              e_constr = ins;
              e_ret = ret';
              e_typ = `Eff;
            };
          ],
        freshNormStageRet ret' )
    (* higher-order functions *)
    | HigherOrder (pi, heap, ins, ret') ->
      ( effectStages
        @ [
            {
              e_evars = existential;
              e_pre = req;
              e_post = mergeState ens (pi, heap);
              e_constr = ins;
              e_ret = ret';
              e_typ = `Fn;
            };
          ],
        freshNormStageRet ret' )
  in
  debug ~at:3 ~title:"normalize step" "%s\n+\n%s\n==>\n%s"
    (string_of_normalisedStagedSpec acc)
    (string_of_staged_spec stagedSpec)
    (string_of_normalisedStagedSpec res);
  res

(* | IndPred {name; _} -> *)
(* failwith (Format.asprintf "cannot normalise predicate %s" name) *)

let (*rec*) normalise_spec_ (acc : normalisedStagedSpec) (spec : spec) :
    normalisedStagedSpec =
  List.fold_left normalise_stagedSpec acc spec
(* match spec with
     | [] -> acc
     | x :: xs ->
       (*let time_1 = Sys.time() in*)
       let acc' = normalise_stagedSpec acc x in
       (*let time_2 = Sys.time() in
       let during = time_2 -. time_1 in
       (
       print_endline (string_of_stages x );
       print_endline ("[testing   Time] " ^ string_of_float ((during) *. 1000.0) ^ " ms\n"));
   *)
       normalise_spec_ acc' xs *)

let rec used_vars_term (t : term) =
  match t with
  | Nil | TTrue | TFalse | UNIT | Num _ -> SSet.empty
  | TList ts | TTupple ts -> SSet.concat (List.map used_vars_term ts)
  | Var s -> SSet.singleton s
  | Rel (_, a, b) | Plus (a, b) | Minus (a, b) | TAnd (a, b) | TOr (a, b) ->
    SSet.union (used_vars_term a) (used_vars_term b)
  | TNot a -> used_vars_term a
  | TApp (_, args) -> SSet.concat (List.map used_vars_term args)
  | TLambda _ -> SSet.empty

let rec used_vars_pi (p : pi) =
  match p with
  | True | False -> SSet.empty
  | Atomic (_, a, b) -> SSet.union (used_vars_term a) (used_vars_term b)
  | And (a, b) | Or (a, b) | Imply (a, b) ->
    SSet.union (used_vars_pi a) (used_vars_pi b)
  | Not a -> used_vars_pi a
  | Predicate (_, t) -> used_vars_term t

let rec used_vars_heap (h : kappa) =
  match h with
  | EmptyHeap -> SSet.empty
  | PointsTo (a, t) -> SSet.add a (used_vars_term t)
  | SepConj (a, b) -> SSet.union (used_vars_heap a) (used_vars_heap b)

let rec used_locs_heap (h : kappa) =
  match h with
  | EmptyHeap -> SSet.empty
  | PointsTo (a, _) -> SSet.singleton a
  | SepConj (a, b) -> SSet.union (used_locs_heap a) (used_locs_heap b)

let used_vars_state (p, h) = SSet.union (used_vars_pi p) (used_vars_heap h)

let used_vars_eff eff =
  SSet.concat
    [
      used_vars_state eff.e_pre;
      used_vars_state eff.e_post;
      SSet.concat (List.map used_vars_term (snd eff.e_constr));
      used_vars_term eff.e_ret;
    ]

let used_vars_norm (_vs, pre, post, ret) =
  SSet.concat [used_vars_state pre; used_vars_state post; used_vars_term ret]

let used_vars (sp : normalisedStagedSpec) =
  let effs, norm = sp in
  SSet.concat (used_vars_norm norm :: List.map used_vars_eff effs)

let rec collect_lambdas_term (t : term) =
  match t with
  | Nil | TTrue | TFalse | UNIT | Num _ -> SSet.empty
  | TList ts | TTupple ts -> SSet.concat (List.map collect_lambdas_term ts)
  | Var _ -> SSet.empty
  | Rel (_, a, b) | Plus (a, b) | Minus (a, b) | TAnd (a, b) | TOr (a, b) ->
    SSet.union (collect_lambdas_term a) (collect_lambdas_term b)
  | TNot a -> collect_lambdas_term a
  | TApp (_, args) -> SSet.concat (List.map collect_lambdas_term args)
  | TLambda l -> SSet.singleton l

let rec collect_lambdas_pi (p : pi) =
  match p with
  | True | False -> SSet.empty
  | Atomic (_, a, b) ->
    SSet.union (collect_lambdas_term a) (collect_lambdas_term b)
  | And (a, b) | Or (a, b) | Imply (a, b) ->
    SSet.union (collect_lambdas_pi a) (collect_lambdas_pi b)
  | Not a -> collect_lambdas_pi a
  | Predicate (_, t) -> collect_lambdas_term t

let rec collect_lambdas_heap (h : kappa) =
  match h with
  | EmptyHeap -> SSet.empty
  | PointsTo (_, t) -> collect_lambdas_term t
  | SepConj (a, b) ->
    SSet.union (collect_lambdas_heap a) (collect_lambdas_heap b)

let collect_lambdas_state (p, h) =
  SSet.union (collect_lambdas_pi p) (collect_lambdas_heap h)

let collect_lambdas_eff eff =
  SSet.concat
    [
      collect_lambdas_state eff.e_pre;
      collect_lambdas_state eff.e_post;
      SSet.concat (List.map collect_lambdas_term (snd eff.e_constr));
      collect_lambdas_term eff.e_ret;
    ]

let collect_lambdas_norm (_vs, pre, post, ret) =
  SSet.concat
    [
      collect_lambdas_state pre;
      collect_lambdas_state post;
      collect_lambdas_term ret;
    ]

let collect_lambdas (sp : normalisedStagedSpec) =
  let effs, norm = sp in
  SSet.concat (collect_lambdas_norm norm :: List.map collect_lambdas_eff effs)

(* this moves existentials inward and removes unused ones *)
let optimize_existentials : normalisedStagedSpec -> normalisedStagedSpec =
 fun (ess, norm) ->
  let rec loop already_used unused acc es =
    match es with
    | [] -> (unused, List.rev acc)
    | e :: rest ->
      let available =
        SSet.diff (SSet.union (SSet.of_list e.e_evars) unused) already_used
      in
      let needed = SSet.diff (used_vars_eff e) already_used in
      let used_ex, unused_ex =
        SSet.partition (fun v -> SSet.mem v needed) available
      in
      loop
        (SSet.union already_used used_ex)
        unused_ex
        ({ e with e_evars = SSet.elements used_ex } :: acc)
        rest
  in
  let unused, es1 = loop SSet.empty SSet.empty [] ess in
  let norm1 =
    let used = used_vars_norm norm in
    let evars, h, p, r = norm in
    let may_be_used = SSet.union (SSet.of_list evars) unused in
    (* unused ones are dropped *)
    let used_ex, _unused_ex =
      SSet.partition (fun v -> SSet.mem v used) may_be_used
    in
    (SSet.elements used_ex, h, p, r)
  in
  (es1, norm1)

(* if we see [ex x; Norm(x->..., ...); ex y; Norm(y->..., ...)] and [x=y] appears somewhere, remove y (the lexicographically larger of the two) *)
(* this does just one iteration. could do to a fixed point *)
let simplify_existential_locations sp =
  let _, ex_loc =
    List.fold_left
      (fun (ex, locs) c ->
        match c with
        | Exists vs -> (SSet.add_seq (List.to_seq vs) ex, locs)
        | Require (p, h)
        | NormalReturn (p, h, _)
        | HigherOrder (p, h, _, _)
        | RaisingEff (p, h, _, _) ->
          ( ex,
            (* used_locs_heap h *)
            used_vars_state (p, h)
            |> SSet.filter (fun l -> SSet.mem l ex)
            |> SSet.union locs ))
      (SSet.empty, SSet.empty) sp
  in
  let eqs =
    List.concat_map
      (fun s ->
        match s with
        | Exists _ -> []
        | Require (p, _)
        | NormalReturn (p, _, _)
        | HigherOrder (p, _, _, _)
        | RaisingEff (p, _, _, _) ->
          pure_to_equalities p)
      sp
  in
  (* if there is an eq between two existential locations, keep only one *)
  List.fold_right
    (fun (a, b) sp ->
      if a <> b && SSet.mem a ex_loc && SSet.mem b ex_loc then
        let smaller = if a < b then a else b in
        let larger = if a < b then b else a in
        let bs = [(larger, Var smaller)] in
        instantiateSpec bs sp
      else sp)
    eqs sp

let normalise_spec sp =
  let r =
    let sp = simplify_existential_locations sp in
    let sp =
      let v = verifier_getAfreeVar "n" in
      let acc = ([], freshNormStageVar v) in
      normalise_spec_ acc sp
    in
    sp
    (* redundant vars may appear due to fresh stages *)
    |> optimize_existentials
  in
  debug ~at:2 ~title:"normalise" "%s\n\n%s" (string_of_spec sp)
    (string_of_normalisedStagedSpec r);
  r

let rec effectStage2Spec (effectStages : effectStage list) : spec =
  match effectStages with
  | [] -> []
  | eff :: xs ->
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

let normalStage2Spec (normalStage : normalStage) : spec =
  let existiental, (p1, h1), (p2, h2), ret = normalStage in
  (match existiental with [] -> [] | _ -> [Exists existiental])
  @ (match (p1, h1) with True, EmptyHeap -> [] | _ -> [Require (p1, h1)])
  @
  match (p2, h2, ret) with
  (*| (True, EmptyHeap, UNIT) -> [] *)
  | _ -> [NormalReturn (p2, h2, ret)]

let rec detectfailedAssertions (spec : spec) : spec =
  match spec with
  | [] -> []
  | Require (pi, heap) :: xs ->
    let pi' = ProversEx.normalize_pure pi in
    (match ProversEx.entailConstrains pi' False with
    | true -> [Require (False, heap)]
    | _ -> Require (pi', heap) :: detectfailedAssertions xs)
  (* higher-order functions *)
  | x :: xs -> x :: detectfailedAssertions xs

let normalisedStagedSpec2Spec (normalisedStagedSpec : normalisedStagedSpec) :
    spec =
  let effS, normalS = normalisedStagedSpec in
  detectfailedAssertions (effectStage2Spec effS @ normalStage2Spec normalS)

(* spec list -> normalisedStagedSpec list *)
let normalise_spec_list_aux1 (specLi : spec list) : normalisedStagedSpec list =
  List.map (fun a -> normalise_spec a) specLi

let normalise_spec_list_aux2 (specLi : normalisedStagedSpec list) : spec list =
  List.map (fun a -> normalisedStagedSpec2Spec a) specLi

let normalise_spec_list (specLi : spec list) : spec list =
  List.map
    (fun a ->
      let normalisedStagedSpec = normalise_spec a in
      normalisedStagedSpec2Spec normalisedStagedSpec)
    specLi

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
