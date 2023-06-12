open Hiptypes
open Pretty

let rec domainOfHeap (h : kappa) : string list =
  match h with
  | EmptyHeap -> []
  | PointsTo (str, _) -> [str]
  | SepConj (k1, k2) -> domainOfHeap k1 @ domainOfHeap k2
(*| MagicWand (k1, k2) -> (domainOfHeap k1) @ (domainOfHeap k2) *)

let rec existStr str li =
  match li with
  | [] -> false
  | x :: xs -> if String.compare x str == 0 then true else existStr str xs

let overlap domain1 domain2 : bool =
  let rec iterateh1 li =
    match li with
    | [] -> false
    | y :: ys -> if existStr y domain2 then true else iterateh1 ys
  in
  iterateh1 domain1

let domainOverlap h1 h2 =
  let domain1 = domainOfHeap h1 in
  let domain2 = domainOfHeap h2 in
  overlap domain1 domain2

let () = assert (overlap ["x"] ["x"] = true)
let () = assert (overlap ["x"] ["y"] = false)
let () = assert (overlap ["x"] [] = false)
let () = assert (overlap ["x"; "y"] ["y"; "z"] = true)

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

let rec kappa_of_list li =
  match li with
  | [] -> EmptyHeap
  | (x, v) :: xs -> SepConj (PointsTo (x, v), kappa_of_list xs)

(* (x, t1) -* (y, t2) *)
let rec deleteFromHeapListIfHas li (x, t1) existential flag :
    (string * term) list * pi =
  match li with
  | [] -> ([], True)
  | (y, t2) :: ys ->
    if String.compare x y == 0 then
      if stricTcompareTerm t2 (Var "_") then (ys, True)
      else
        match (t1, t2) with
        (* x->11 -* x-> z   ~~~>   (emp, true) *)
        | Num _, Var t2Str ->
          if existStr t2Str existential then (ys, True)
          else (ys, Atomic (EQ, t1, t2))
        (* x-> z -* x-> 11   ~~~>  (emp, z=11) *)
        | Var t2Str, Num _ ->
          if String.compare t2Str "_" == 0 then (ys, True)
          else (ys, Atomic (EQ, t1, t2))
        | _, _ ->
          if stricTcompareTerm t1 t2 || stricTcompareTerm t1 (Var "_") then
            (ys, True)
          else if flag then (ys, Atomic (EQ, t1, t2))
          else (ys, Atomic (EQ, t1, t2))
    else
      let res, uni = (deleteFromHeapListIfHas ys (x, t1) existential) flag in
      ((y, t2) :: res, uni)

(* h1 * h |- h2, returns h and unificiation
   x -> 3 |- x -> z   -> (emp, true )
   x -> z |- x -> 3   -> (emp, z = 3)
*)
let normaliseMagicWand h1 h2 existential flag : kappa * pi =
  let listOfHeap1 = list_of_heap h1 in
  let listOfHeap2 = list_of_heap h2 in
  let rec helper (acc : (string * term) list * pi) li =
    let heapLi, unification = acc in
    match li with
    | [] -> acc
    | (x, v) :: xs ->
      let heapLi', unification' =
        deleteFromHeapListIfHas heapLi (x, v) existential flag
      in
      helper (heapLi', And (unification, unification')) xs
  in
  let temp, unifinication = helper (listOfHeap2, True) listOfHeap1 in
  (normaliseHeap (kappa_of_list temp), unifinication)

let normalise_stagedSpec (acc : normalisedStagedSpec) (stagedSpec : stagedSpec)
    : normalisedStagedSpec =
  (*print_endline("\nnormalise_stagedSpec =====> " ^ string_of_normalisedStagedSpec(acc));
    print_endline("\nadding  " ^ string_of_stages (stagedSpec));
  *)
  let effectStages, normalStage = acc in
  let existential, req, ens, ret = normalStage in
  match stagedSpec with
  | Exists li -> (effectStages, (existential @ li, req, ens, ret))
  | Require (p3, h3) ->
    let p2, h2 = ens in
    let magicWandHeap, unification =
      normaliseMagicWand h2 h3 existential true
    in

    (*print_endline (string_of_kappa (magicWandHeap) ^ " magic Wand "); *)

    (* not only need to get the magic wand, but also need to delete the common part from h2*)
    let h2', unification' = normaliseMagicWand h3 h2 existential false in

    let normalStage' =
      ( existential,
        mergeState req (And (p3, unification), magicWandHeap),
        (ProversEx.normalize_pure (And (p2, unification')), h2'),
        ret )
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
  | Eq (a, b) | Plus (a, b) | Minus (a, b) ->
    SSet.union (used_vars_term a) (used_vars_term b)
  | TApp (_, args) -> SSet.concat (List.map used_vars_term args)

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

let normalise_spec sp =
  let v = verifier_getAfreeVar ~from:"n" () in
  let acc = ([], freshNormStageVar v) in
  let sp1 = normalise_spec_ acc sp in
  sp1
  (* redundant vars may appear due to fresh stages *)
  |> optimize_existentials

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

let%expect_test "normalise spec" =
  verifier_counter_reset ();
  let test s =
    let n = normalise_spec s in
    Format.printf "%s\n==>\n%s\n@." (string_of_spec s)
      (string_of_normalisedStagedSpec n)
  in
  print_endline "--- norm\n";
  test
    [
      NormalReturn (True, PointsTo ("x", Num 2), UNIT);
      Require (True, PointsTo ("x", Num 1));
    ];
  test
    [
      Require (True, PointsTo ("x", Num 1));
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      Require (True, PointsTo ("y", Num 2));
      NormalReturn (True, PointsTo ("y", Num 2), UNIT);
    ];
  test
    [
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), UNIT);
    ];
  test
    [
      NormalReturn
        (True, SepConj (PointsTo ("x", Num 1), PointsTo ("y", Num 2)), UNIT);
      Require (True, PointsTo ("x", Var "a"));
      NormalReturn (True, PointsTo ("x", Plus (Var "a", Num 1)), UNIT);
    ];
  test
    [
      NormalReturn (Atomic (EQ, Var "a", Num 3), PointsTo ("y", Var "a"), UNIT);
      Require (Atomic (EQ, Var "b", Var "a"), PointsTo ("x", Var "b"));
      NormalReturn (True, PointsTo ("x", Plus (Var "b", Num 1)), UNIT);
    ];
  print_endline "--- eff\n";
  test
    [
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      Require (True, PointsTo ("x", Var "1"));
      RaisingEff (True, PointsTo ("x", Num 1), ("E", [Num 3]), UNIT);
      NormalReturn (True, PointsTo ("y", Num 2), UNIT);
    ];
  test
    [
      NormalReturn (True, PointsTo ("x", Num 1), UNIT);
      HigherOrder (True, EmptyHeap, ("f", [Num 3]), UNIT);
      NormalReturn (True, PointsTo ("y", Num 2), UNIT);
    ];
  [%expect
    {|
  --- norm

  Norm(x->2, ()); req x->1
  ==>
  req 2=1; Norm(1=2, ())

  req x->1; Norm(x->1, ()); req y->2; Norm(y->2, ())
  ==>
  req x->1*y->2; Norm(x->1*y->2, ())

  Norm(x->1, ()); req x->a; Norm(x->a+1, ())
  ==>
  req 1=a; Norm(x->a+1 /\ a=1, ())

  Norm(x->1*y->2, ()); req x->a; Norm(x->a+1, ())
  ==>
  req 1=a; Norm(y->2*x->a+1 /\ a=1, ())

  Norm(y->a /\ a=3, ()); req x->b /\ b=a; Norm(x->b+1, ())
  ==>
  req x->b /\ b=a; Norm(y->a*x->b+1 /\ a=3, ())

  --- eff

  Norm(x->1, ()); req x->1; E(x->1, (3), ()); Norm(y->2, ())
  ==>
  req 1=1; E(x->1 /\ 1=1, (3), ()); req emp; Norm(y->2, ())

  Norm(x->1, ()); f$(emp, (3), ()); Norm(y->2, ())
  ==>
  req emp; f$(x->1, (3), ()); req emp; Norm(y->2, ())
|}]
