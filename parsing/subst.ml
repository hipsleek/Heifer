open Hiptypes

let rec findNewName str vb_li =
  match vb_li with
  | [] -> str
  | (name, new_name) :: xs ->
    if String.compare name str == 0 then new_name else findNewName str xs

let rec instantiateExistientalVar_aux (li : string list)
    (bindings : (string * string) list) : string list =
  match li with
  | [] -> []
  | str :: xs ->
    let str' = findNewName str bindings in
    str' :: instantiateExistientalVar_aux xs bindings

let rec instantiateExistientalVar (spec : normalisedStagedSpec)
    (bindings : (string * string) list) : normalisedStagedSpec =
  let effS, normalS = spec in
  match effS with
  | [] ->
    (* print_endline ("nROMRAL STATGE"); *)
    let ex, req, ens = normalS in
    ([], (instantiateExistientalVar_aux ex bindings, req, ens))
  | eff :: xs ->
    (* print_endline ("EFF STATGE"); *)
    let rest, norm' = instantiateExistientalVar (xs, normalS) bindings in
    ( { eff with e_evars = instantiateExistientalVar_aux eff.e_evars bindings }
      :: rest,
      norm' )

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

  | TTimes (t1, t2) -> TTimes (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | TDiv (t1, t2) -> TDiv (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | Minus (t1, t2) ->
    Minus (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | TPower (t1, t2) ->
    TPower (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | TApp (t1, t2) -> TApp (t1, List.map (instantiateTerms bindings) t2)
  | TLambda (n, params, sp) ->
    TLambda (n, params, instantiateSpecList bindings sp)

and instantiatePure (bindings : (string * core_value) list) (pi : pi) : pi =
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

and instantiateHeap (bindings : (string * core_value) list) (kappa : kappa) :
    kappa =
  match kappa with
  | EmptyHeap -> kappa
  | PointsTo (str, t1) ->
    let binding = findbinding str bindings in
    let newName = match binding with Var str1 -> str1 | _ -> str in
    PointsTo (newName, instantiateTerms bindings t1)
  | SepConj (k1, k2) ->
    SepConj (instantiateHeap bindings k1, instantiateHeap bindings k2)

and instantiate_state bindings (p, h) =
  (instantiatePure bindings p, instantiateHeap bindings h)

and instantiateStages (bindings : (string * core_value) list)
    (stagedSpec : stagedSpec) : stagedSpec =
  match stagedSpec with
  | Exists _ -> stagedSpec
  | Require (pi, kappa) ->
    Require (instantiatePure bindings pi, instantiateHeap bindings kappa)
  (* higher-order functions *)
  | NormalReturn (pi, kappa) ->
    NormalReturn (instantiatePure bindings pi, instantiateHeap bindings kappa)
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

and instantiateSpec (bindings : (string * core_value) list) (sepc : spec) : spec
    =
  List.map (fun a -> instantiateStages bindings a) sepc

and instantiateSpecList (bindings : (string * core_value) list)
    (sepcs : disj_spec) : disj_spec =
  List.map (fun a -> instantiateSpec bindings a) sepcs

let rec used_vars_term (t : term) =
  match t with
  | Nil | TTrue | TFalse | UNIT | Num _ -> SSet.empty
  | TList ts | TTupple ts -> SSet.concat (List.map used_vars_term ts)
  | Var s -> SSet.singleton s
  | Rel (_, a, b) | Plus (a, b) | Minus (a, b) | TAnd (a, b) | TOr (a, b) | TPower (a, b) |  TTimes (a, b) | TDiv (a, b)  ->
    SSet.union (used_vars_term a) (used_vars_term b)
  | TNot a -> used_vars_term a
  | TApp (_, args) -> SSet.concat (List.map used_vars_term args)
  | TLambda (_lid, params, spec) ->
    SSet.diff (used_vars_disj_spec spec) (SSet.of_list params)

and used_vars_pi (p : pi) =
  match p with
  | True | False -> SSet.empty
  | Atomic (_, a, b) -> SSet.union (used_vars_term a) (used_vars_term b)
  | And (a, b) | Or (a, b) | Imply (a, b) ->
    SSet.union (used_vars_pi a) (used_vars_pi b)
  | Not a -> used_vars_pi a
  | Predicate (_, t) -> used_vars_term t

and used_vars_heap (h : kappa) =
  match h with
  | EmptyHeap -> SSet.empty
  | PointsTo (a, t) -> SSet.add a (used_vars_term t)
  | SepConj (a, b) -> SSet.union (used_vars_heap a) (used_vars_heap b)

and used_vars_state (p, h) = SSet.union (used_vars_pi p) (used_vars_heap h)

and used_vars_eff eff =
  SSet.concat
    [
      used_vars_state eff.e_pre;
      used_vars_state eff.e_post;
      SSet.concat (List.map used_vars_term (snd eff.e_constr));
      used_vars_term eff.e_ret;
    ]

and used_vars_norm (_vs, pre, post) =
  SSet.concat [used_vars_state pre; used_vars_state post]

and used_vars (sp : normalisedStagedSpec) =
  let effs, norm = sp in
  SSet.concat (used_vars_norm norm :: List.map used_vars_eff effs)

and used_vars_stage (s : stagedSpec) =
  match s with
  | Require (p, h) | NormalReturn (p, h) ->
    SSet.union (used_vars_pi p) (used_vars_heap h)
  | Exists vs -> SSet.of_list vs
  | HigherOrder (p, h, (f, a), t) | RaisingEff (p, h, (f, a), t) ->
    SSet.concat
      [
        used_vars_pi p;
        used_vars_heap h;
        SSet.concat (List.map used_vars_term a);
        SSet.of_list [f];
        used_vars_term t;
      ]

and used_vars_spec (sp : spec) = SSet.concat (List.map used_vars_stage sp)

and used_vars_disj_spec (d : disj_spec) =
  SSet.concat (List.map used_vars_spec d)

(* if alpha_equiv(t1, t2), then hash t1 = hash t2 *)
let hash_lambda t =
  match t with
  | TLambda (_id, params, spec) ->
    let bs = List.mapi (fun i p -> (p, "l" ^ string_of_int i)) params in
    let renamed =
      instantiateSpecList (List.map (fun (p, v) -> (p, Var v)) bs) spec
    in
    let n = TLambda ("id", List.map snd bs, renamed) in
    (* Format.printf "renamed %s@." (string_of_term n); *)
    Hashtbl.hash n
  | _ -> failwith (Format.asprintf "not a lambda: %s" "(cannot print)")

let rec getExistentialVar (spec : normalisedStagedSpec) : string list =
  let effS, normalS = spec in
  match effS with
  | [] ->
    let ex, _, _ = normalS in
    ex
  | eff :: xs -> eff.e_evars @ getExistentialVar (xs, normalS)
