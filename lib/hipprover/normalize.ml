open Hipcore_typed
open Typedhip
open Debug
open Variables
open Utils
open Syntax
open Rewriting
open Rules

(* set the res var's type to Any, the eq smart constructor will
   set its type to the result value *)
let res_var = res_var ~typ:Any

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
  (Bind ((Binder.uvar "x"), ens ~p:(eq res_var (Term.uvar "r")) (), Staged.uvar "f"))
  (fun sub ->
    let x = sub "x" |> Binder.of_uterm in
    let r = sub "r" |> Term.of_uterm in
    let f = sub "f" |> Staged.of_uterm in
    if is_lambda_term r then
      Bind (x, NormalReturn (eq res_var r, emp), f)
    else
      Subst.subst_free_vars [(ident_of_binder x, r)] f)

let norm_bind_trivial = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Staged.uvar "f",
    NormalReturn (eq res_var (Term.uvar "r"), emp)))
  (fun sub ->
    let x = sub "x" |> Binder.of_uterm in
    let r = sub "r" |> Term.of_uterm in
    let f = sub "f" |> Staged.of_uterm in
    if (var_of_binder x).term_desc = r.term_desc then f
    else Bind (x, f, ens ~p:(eq res_var r) ()))

let norm_bind_disj = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Disjunction (Staged.uvar "f1", Staged.uvar "f2"), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let f1 = Staged.of_uterm (sub "f1") in
    let f2 = Staged.of_uterm (sub "f2") in
    let fk = Staged.of_uterm (sub "fk") in
    Disjunction (Bind (x, f1, fk), Bind (x, f2, fk)))

let norm_seq_ens_disj = Staged.dynamic_rule
  (Sequence (NormalReturn (Pure.uvar "p", Heap.uvar "h"), Disjunction (Staged.uvar "f1", Staged.uvar "f2")))
  (fun sub ->
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f1 = Staged.of_uterm (sub "f1") in
    let f2 = Staged.of_uterm (sub "f2") in
    let ens_stage = NormalReturn (p, h) in
    Disjunction (Sequence (ens_stage, f1), Sequence (ens_stage, f2)))

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

(* TODO: generalize to bind_assoc? *)
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

let norm_seq_val = Staged.rule
  (Sequence (NormalReturn (eq res_var (Term.uvar "r"), emp), Staged.uvar "f"))
  (Staged.uvar "f")

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
(* let norm_bind_seq_ens = Staged.dynamic_rule
  (Bind (Binder.uvar "x", Sequence (NormalReturn (Pure.uvar "p", Heap.uvar "h"), Staged.uvar "f"), Staged.uvar "fk"))
  (fun sub ->
    let x = Binder.of_uterm (sub "x") in
    let p = Pure.of_uterm (sub "p") in
    let h = Heap.of_uterm (sub "h") in
    let f = Staged.of_uterm (sub "f") in
    let fk = Staged.of_uterm (sub "fk") in
    Sequence (NormalReturn (p, h), Bind (x, f, fk))) *)

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

let norm_ens_pure_ens_pure = Staged.dynamic_rule
  (seq [NormalReturn (Pure.uvar "p1", emp); NormalReturn (Pure.uvar "p2", emp)])
  (fun sub ->
    let p1 = Pure.of_uterm (sub "p1") in
    let p2 = Pure.of_uterm (sub "p2") in
    if is_eq_res p1 || is_eq_res p2 then
      seq [NormalReturn (p1, emp); NormalReturn (p2, emp)]
    else
      NormalReturn (And (p1, p2), emp))

let norm_seq_ens_pure_ens_pure = Staged.dynamic_rule
  (seq [NormalReturn (Pure.uvar "p1", emp); NormalReturn (Pure.uvar "p2", emp); Staged.uvar "f"])
  (fun sub ->
    let p1 = Pure.of_uterm (sub "p1") in
    let p2 = Pure.of_uterm (sub "p2") in
    let f = Staged.of_uterm (sub "f") in
    if is_eq_res p1 || is_eq_res p2 then
      seq [NormalReturn (p1, emp); NormalReturn (p2, emp); f]
    else
      seq [NormalReturn (And (p1, p2), emp); f])

let norm_ens_heap_ens_heap = Staged.rule
  (seq [NormalReturn (True, Heap.uvar "h1"); NormalReturn (True, Heap.uvar "h2")])
  (NormalReturn (True, SepConj (Heap.uvar "h1", Heap.uvar "h2")))

let norm_seq_ens_heap_ens_heap = Staged.rule
  (seq [NormalReturn (True, Heap.uvar "h1"); NormalReturn (True, Heap.uvar "h2"); Staged.uvar "f"])
  (seq [NormalReturn (True, SepConj (Heap.uvar "h1", Heap.uvar "h2")); Staged.uvar "f"])

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

(* this rule is not proven in Coq formulization yet *)
let norm_seq_assoc = Staged.rule
  (seq [seq [Staged.uvar "f1"; Staged.uvar "f2"]; Staged.uvar "f3"])
  (seq [Staged.uvar "f1"; Staged.uvar "f2"; Staged.uvar "f3"])

let norm_bind_seq_assoc =
  let x = Binder.uvar "x" in
  let f1 = Staged.uvar "f1" in
  let f2 = Staged.uvar "f2" in
  let f3 = Staged.uvar "f3" in
  Staged.rule (seq [bind x f1 f2; f3]) (bind x f1 (seq [f2; f3]))

let norm_seq_bind_assoc =
  let x = Binder.uvar "x" in
  let f1 = Staged.uvar "f1" in
  let f2 = Staged.uvar "f2" in
  let f3 = Staged.uvar "f3" in
  Staged.rule (bind x (seq [f1; f2]) f3) (seq [f1; bind x f2 f3])

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
  (* norm_bind_seq_ens; *)
]

let normalization_rules_seq = [
  norm_seq_val;
  norm_seq_ens_ex;
  norm_seq_ens_all;
  norm_seq_ens_seq_all;
  norm_seq_ens_disj;
]

let normalization_rules_assoc = [
  norm_bind_assoc_ens;
  norm_seq_assoc;
  norm_bind_seq_assoc;
  norm_seq_bind_assoc;
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
  normalization_rules_assoc;
  normalization_rules_permute_ens;
]

let normalization_rules_lhs_only = [
  norm_seq_all;
  norm_seq_ex;
]

let normalization_rules_rhs_only = []

let normalization_rules_lhs = normalization_rules @ normalization_rules_lhs_only
let normalization_rules_rhs = normalization_rules @ normalization_rules_rhs_only

(*
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
  ] *)

(* the main entry point *)
let normalize_spec_with (rules : rule list) (spec : staged_spec) : staged_spec =
  let@ _ = Hipcore_typed.Globals.Timing.(time norm) in
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
    let input = bind ("x", Int) (disj [f1; f2]) fk in
    (* let output = disj [bind "x" f1 fk; bind "x" f2 fk] in *)
    test norm_bind_disj input;
    [%expect
      {| (let x = (ens res=1) in (ens res=(x + 1))) \/ (let x = (ens res=2) in (ens res=(x + 1))) |}]
  in
  let _ =
    let f = ens ~p:(eq res_var (num 1)) () in
    let fk = ens ~p:(eq res_var (plus (var "x") (num 1))) () in
    let input = bind ("x", Int) (seq [f; f]) fk in
    test norm_seq_bind_assoc input;
    [%expect
      {| ens res=1; let x2 = (ens res=1) in (ens res=(x2 + 1)) |}]
  in
  let _ =
    let ens_heap = NormalReturn (True, PointsTo ("x", num 1)) in
    let ens_pure = NormalReturn (eq (var "x" ~typ:Int) (num 1), emp) in
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
    let input = Bind (("x", Int), Exists (("y", Int), (ens ~p:(eq (v "res") (num 2)) ())), ens ~p:(eq (v "x") (num 1)) ()) in
    test norm_bind_ex input;
    [%expect
      {| ex y. (let x = (ens res=2) in (ens x=1)) |}]
  in
  let _ =
    let input = Bind (("x", Int), ForAll (("y", Int), (ens ~p:(eq (v "res") (num 2)) ())), ens ~p:(eq (v "x") (num 1)) ()) in
    test norm_bind_all input;
    [%expect
      {| forall y. (let x = (ens res=2) in (ens x=1)) |}]
  in
  let _ =
    let input = Bind (("x", Int), ens ~p:(eq (v "y") (num 2)) (), ens ~p:(eq (v "res") (v "x")) ()) in
    test norm_bind_trivial input;
    [%expect
      {| ens y=2 |}];

    let input = Bind (("z", Int), ens ~p:(eq (v "y") (num 2)) (), ens ~p:(eq (v "res") (v "x")) ()) in
    test norm_bind_trivial input;
    [%expect
      {| let z = (ens y=2) in (ens res=x) |}]
  in
  ()
