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
  | Minus (t1, t2) ->
    Minus (instantiateTerms bindings t1, instantiateTerms bindings t2)
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
