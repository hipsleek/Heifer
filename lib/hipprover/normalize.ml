open Hipcore
open Hiptypes
open Debug
open Variables
open Utils
open Syntax
open Rewriting
open Rules

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
*)

let split_eq_res_pi (p : pi) : pi option * pi =
  match Lists.find_delete_opt is_eq_res (conjuncts_of_pi p) with
  | None -> None, p
  | Some (eq_res, pure) ->
      let pure = match pure with
        | [] -> True
        | _ :: _ -> conj pure
      in
      Some eq_res, pure

let split_ens_aux (p : pi) (k : kappa) : staged_spec =
  let eq_res, pure = split_eq_res_pi p in
  let ens_eq_res_opt = match eq_res with
    | None -> None
    | Some eq_res -> Some (NormalReturn (eq_res, EmptyHeap))
  in
  let ens_pure_opt = match pure with
    | True -> None
    | _ -> Some (NormalReturn (pure, EmptyHeap))
  in
  let ens_heap_opt = match k with
    | EmptyHeap -> None
    | _ -> Some (NormalReturn (True, k))
  in
  let ens_stages = Options.concat_option [ens_pure_opt; ens_heap_opt; ens_eq_res_opt] in
  if List.is_empty ens_stages then ens () else seq ens_stages

let split_ens_visitor =
  object
    inherit [_] map_spec
    method! visit_NormalReturn _ p k = split_ens_aux p k
  end

let split_ens = split_ens_visitor#visit_staged_spec ()

let norm_bind_val = Staged.dynamic_rule
  (Bind (Binder.uvar "x", NormalReturn (eq res_var (Term.uvar "r"), emp), Staged.uvar "f"))
  (fun sub ->
    let x = sub "x" |> Binder.of_uterm in
    let r = sub "r" |> Term.of_uterm in
    let f = sub "f" |> Staged.of_uterm in
    if is_lambda_term r then
      Bind (x, NormalReturn (eq res_var r, emp), f)
    else
      Subst.subst_free_vars [(x, r)] f)

let norm_bind_trivial = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Staged.uvar "f",
    NormalReturn (eq res_var (Term.uvar "r"), emp)))
  (fun sub ->
    let x = sub "x" |> Binder.of_uterm in
    let r = sub "r" |> Term.of_uterm in
    let f = sub "f" |> Staged.of_uterm in
    if Var x = r then f
    else Bind (x, f, ens ~p:(eq res_var r) ()))

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

let norm_bind_ex = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Exists (Binder.uvar "x1", (Staged.uvar "f")), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let x1 = Binder.of_uterm (sub "x1") in
    let f = Staged.of_uterm (sub "f") in
    let fk = Staged.of_uterm (sub "fk") in
    Exists (x1, Bind (x, f, fk)))

let norm_bind_all = Staged.dynamic_rule
  (Bind (Binder.uvar "x", ForAll (Binder.uvar "x1", (Staged.uvar "f")), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let x1 = Binder.of_uterm (sub "x1") in
    let f = Staged.of_uterm (sub "f") in
    let fk = Staged.of_uterm (sub "fk") in
    ForAll (x1, Bind (x, f, fk)))

let norm_bind_assoc_ens = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Bind (Binder.uvar "y", NormalReturn (Pure.uvar "p", Heap.uvar "h"), Staged.uvar "f1"), Staged.uvar "f2"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let y = Binder.of_uterm (sub "y") in
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f1 = Staged.of_uterm (sub "f1") in
    let f2 = Staged.of_uterm (sub "f2") in
    Bind (y, NormalReturn (p, h), Bind (x, f1, f2)))

let norm_seq_ens_ex = Staged.dynamic_rule
  (Sequence (NormalReturn (Pure.uvar "p", Heap.uvar "h"), Exists (Binder.uvar "x", (Staged.uvar "f"))))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f = Staged.of_uterm (sub "f") in
    Exists (x, Sequence (NormalReturn (p, h), f)))

let norm_seq_ens_all = Staged.dynamic_rule
  (Sequence (NormalReturn (Pure.uvar "p", Heap.uvar "h"), ForAll (Binder.uvar "x", (Staged.uvar "f"))))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f = Staged.of_uterm (sub "f") in
    ForAll (x, Sequence (NormalReturn (p, h), f)))

let norm_seq_ens_seq_all = Staged.dynamic_rule
  (Sequence (NormalReturn (Pure.uvar "p", Heap.uvar "h"), Sequence (ForAll (Binder.uvar "x", (Staged.uvar "f")), Staged.uvar "fk")))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f = Staged.of_uterm (sub "f") in
    let fk = Staged.of_uterm (sub "fk") in
    ForAll (x, seq [NormalReturn (p, h); f; fk]))

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

let norm_ens_heap_ens_pure = Staged.dynamic_rule
  (seq [NormalReturn (True, Heap.uvar "h"); NormalReturn (Pure.uvar "p", emp)])
  (fun sub ->
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    if is_eq_res p then
      seq [NormalReturn (True, h); NormalReturn (p, emp)]
    else
      seq [NormalReturn (p, emp); NormalReturn (True, h)])

let norm_seq_ens_heap_ens_pure = Staged.dynamic_rule
  (seq [NormalReturn (True, Heap.uvar "h"); NormalReturn (Pure.uvar "p", emp); Staged.uvar "f"])
  (fun sub ->
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f = Staged.of_uterm (sub "f") in
    if is_eq_res p then
      seq [NormalReturn (True, h); NormalReturn (p, emp); f]
    else
      seq [NormalReturn (p, emp); NormalReturn (True, h); f])

let norm_ens_pure_ens_pure = Staged.rule
  (seq [NormalReturn (Pure.uvar "p1", emp); NormalReturn (Pure.uvar "p2", emp)])
  (NormalReturn (And (Pure.uvar "p1", Pure.uvar "p2"), emp))

let norm_seq_ens_pure_ens_pure = Staged.rule
  (seq [NormalReturn (Pure.uvar "p1", emp); NormalReturn (Pure.uvar "p2", emp); Staged.uvar "f"])
  (seq [NormalReturn (And (Pure.uvar "p1", Pure.uvar "p2"), emp); Staged.uvar "f"])

let norm_ens_heap_ens_heap = Staged.rule
  (seq [NormalReturn (True, Heap.uvar "h1"); NormalReturn (True, Heap.uvar "h2")])
  (NormalReturn (True, SepConj (Heap.uvar "h1", Heap.uvar "h2")))
let norm_seq_ens_heap_ens_heap = Staged.rule
  (seq [NormalReturn (True, Heap.uvar "h1"); NormalReturn (True, Heap.uvar "h2"); Staged.uvar "f"])
  (seq [NormalReturn (True, SepConj (Heap.uvar "h1", Heap.uvar "h2")); Staged.uvar "f"])

(* this rule is not proven in Coq formulization yet *)
let norm_seq_assoc = Staged.rule
  (seq [seq [Staged.uvar "f1"; Staged.uvar "f2"]; Staged.uvar "f3"])
  (seq [Staged.uvar "f1"; Staged.uvar "f2"; Staged.uvar "f3"])

let norm_seq_ens_emp = Staged.rule
  (seq [ens (); Staged.uvar "f"])
  (Staged.uvar "f")

let norm_seq_req_emp = Staged.rule
  (seq [req (); Staged.uvar "f"])
  (Staged.uvar "f")

let norm_seq_all = Staged.dynamic_rule
  (Sequence (ForAll (Binder.uvar "x", Staged.uvar "f"), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let f = Staged.of_uterm (sub "f") in
    let fk = Staged.of_uterm (sub "fk") in
    ForAll (x, Sequence (f, fk)))
let norm_seq_ex = Staged.dynamic_rule
  (Sequence (Exists (Binder.uvar "x", Staged.uvar "f"), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let f = Staged.of_uterm (sub "f") in
    let fk = Staged.of_uterm (sub "fk") in
    Exists (x, Sequence (f, fk)))

(* this can be applied on both side *)
let normalization_rules_empty = [
  norm_seq_ens_emp;
  norm_seq_req_emp;
]

let normalization_rules_bind = [
  norm_bind_val;
  norm_bind_trivial;
  norm_bind_disj;
  norm_bind_req;
  norm_bind_ex;
  norm_bind_all;
  norm_bind_seq_ens;
  norm_bind_assoc_ens;
]

let normalization_rules_seq = [
  norm_seq_ens_ex;
  norm_seq_ens_all;
  norm_seq_ens_seq_all;
  norm_seq_assoc;
]

let normalization_rules_permute_ens = [
  norm_ens_heap_ens_pure;
  norm_seq_ens_heap_ens_pure;
  norm_ens_pure_ens_pure;
  norm_seq_ens_pure_ens_pure;
  norm_ens_heap_ens_heap;
  norm_seq_ens_heap_ens_heap;
]

let normalization_rules = List.concat [
  normalization_rules_empty;
  normalization_rules_bind;
  normalization_rules_seq;
  normalization_rules_permute_ens;
]

let normalization_rules_lhs_only = [
  norm_seq_all;
  norm_seq_ex;
]

let normalization_rules_rhs_only = []

let normalization_rules_lhs = normalization_rules @ normalization_rules_lhs_only
let normalization_rules_rhs = normalization_rules @ normalization_rules_rhs_only

let norm_bind_val =
  let open Rewriting2 in
  ( bind __ (ens (eq (var "res") __) emp) __,
    fun x r f ->
      let open Syntax in
      if is_lambda_term r then Bind (x, NormalReturn (eq res_var r, emp), f)
      else Subst.subst_free_vars [(x, r)] f )

let norm_db2 : _ Rewriting2.database =
  Rewriting2.[
    norm_bind_val
  ]

(* the main entry point *)
let normalize_spec_with (rules : rule list) (spec : staged_spec) : staged_spec =
  let@ _ = Globals.Timing.(time norm) in
  let@ _ =
    span (fun r -> debug
      ~at:1
      ~title:"normalize_spec"
      "%s\n==>\n%s"
      (Pretty.string_of_staged_spec spec)
      (string_of_result Pretty.string_of_staged_spec r))
  in
  let spec = split_ens spec in
  let spec = Staged.of_uterm (autorewrite rules (Staged spec)) in
  (* let spec = Rewriting2.(autorewrite staged norm_db2 spec) in *)
  spec

let normalize_spec = normalize_spec_with normalization_rules
let normalize_spec_lhs = normalize_spec_with normalization_rules_lhs
let normalize_spec_rhs = normalize_spec_with normalization_rules_rhs

let%expect_test "rules" =
  let test rule input =
    let input = Staged input in
    let output = autorewrite [rule] input in
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
  let _ =
    let ens_heap = NormalReturn (True, PointsTo ("x", num 1)) in
    let ens_pure = NormalReturn (eq (Var "x") (num 1), emp) in
    let input = seq [ens_heap; ens_pure] in
    test norm_ens_heap_ens_pure input;
    [%expect
      {|
      ens x=1; ens x->1
      |}]
  in
  let _ =
    let ens_heap = NormalReturn (True, PointsTo ("x", num 1)) in
    let ens_res = NormalReturn (eq_res (num 69), emp) in
    let input = seq [ens_heap; ens_res] in
    test norm_ens_heap_ens_pure input;
    [%expect
      {|
      ens x->1; ens res=69
      |}]
  in
  let _ =
    let ens_heap = NormalReturn (True, PointsTo ("x", num 1)) in
    let ens_res = NormalReturn (eq_res (num 69), emp) in
    let f = NormalReturn (eq_res (num 42), emp) in
    let input = seq [ens_heap; ens_res; f] in
    test norm_seq_ens_heap_ens_pure input;
    [%expect
      {|
      ens x->1; ens res=69; ens res=42
      |}]
  in
  let _ =
    let input = Bind ("x", Exists ("y", (ens ~p:(eq (v "res") (num 2)) ())), ens ~p:(eq (v "x") (num 1)) ()) in
    test norm_bind_ex input;
    [%expect
      {| ex y. (let x = (ens res=2) in (ens x=1)) |}]
  in
  let _ =
    let input = Bind ("x", ForAll ("y", (ens ~p:(eq (v "res") (num 2)) ())), ens ~p:(eq (v "x") (num 1)) ()) in
    test norm_bind_all input;
    [%expect
      {| forall y. (let x = (ens res=2) in (ens x=1)) |}]
  in
  let _ =
    let input = Bind ("x", ens ~p:(eq (v "y") (num 2)) (), ens ~p:(eq (v "res") (v "x")) ()) in
    test norm_bind_trivial input;
    [%expect
      {| ens y=2 |}];

    let input = Bind ("z", ens ~p:(eq (v "y") (num 2)) (), ens ~p:(eq (v "res") (v "x")) ()) in
    test norm_bind_trivial input;
    [%expect
      {| let z = (ens y=2) in (ens res=x) |}]
  in
  ()