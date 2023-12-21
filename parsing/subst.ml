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
  | (EffHOStage eff) :: xs ->
    (* print_endline ("EFF STATGE"); *)
    let rest, norm' = instantiateExistientalVar (xs, normalS) bindings in
    ( EffHOStage { eff with e_evars = instantiateExistientalVar_aux eff.e_evars bindings }
      :: rest,
      norm' )

  | (TryCatchStage tc) :: xs -> 
    let rest, norm' = instantiateExistientalVar (xs, normalS) bindings in
    ( TryCatchStage { tc with tc_evars = instantiateExistientalVar_aux tc.tc_evars bindings }
      :: rest,
      norm' )


let rec findbinding str vb_li =
  match vb_li with
  | [] -> Var str
  | (name, v) :: xs ->
    if String.compare name str == 0 then v else findbinding str xs

  let sub_visitor bindings =
    object (self)
      inherit [_] map_spec

      method! visit_Exists _ v = Exists v

      method! visit_PointsTo _ (str, t1) =
        let binding = findbinding str bindings in
        let newName = match binding with Var str1 -> str1 | _ -> str in
        PointsTo (newName, self#visit_term () t1)

      method! visit_HigherOrder _ (pi, kappa, (str, basic_t_list), ret) =
        let constr =
          match List.assoc_opt str bindings with Some (Var s) -> s | _ -> str
        in
        HigherOrder
          ( self#visit_pi () pi,
            self#visit_kappa () kappa,
            (constr, List.map (fun bt -> self#visit_term () bt) basic_t_list),
            self#visit_term () ret )

      method! visit_Var _ v =
        let binding = findbinding v bindings in
        (* Format.printf "replacing %s with %s under %s@." str (string_of_term binding) (string_of_list (string_of_pair Fun.id string_of_term) bindings); *)
        binding
    end

let instantiateTerms (bindings : (string * core_value) list) (t : term) :
    term =
  (sub_visitor bindings)#visit_term () t

let instantiateSpecList (bindings : (string * core_value) list) (t : disj_spec) : disj_spec =
  (sub_visitor bindings)#visit_disj_spec () t

let instantiateSpec (bindings : (string * core_value) list) (t : spec) : spec =
  (sub_visitor bindings)#visit_spec () t

let instantiate_state (bindings : (string * core_value) list) (t : state) : state =
  (sub_visitor bindings)#visit_state () t

let instantiatePure (bindings : (string * core_value) list) (t : pi) :
    pi =
  (sub_visitor bindings)#visit_pi () t

let instantiateHeap (bindings : (string * core_value) list) (t : kappa) :
    kappa =
  (sub_visitor bindings)#visit_kappa () t

let instantiateStages (bindings : (string * core_value) list) (t : stagedSpec) : stagedSpec =
  (sub_visitor bindings)#visit_stagedSpec () t

(* for each variable, find how many times it is used and what other terms it is equal to *)
(* TODO generalise to related to *)
let count_uses_and_equalities =
  let add _k a b =
    match (a, b) with
    | None, None -> None
    | Some a, None | None, Some a -> Some a
    | Some (a1, a2), Some (b1, b2) -> Some (a1 + b1, a2 @ b2)
  in
  let zero = SMap.empty in
  let plus = SMap.merge add in
  let vis =
    object (self)
      inherit [_] reduce_normalised as super
      method zero = zero
      method plus = plus

      method! visit_Atomic _ op a b =
        match op, a, b with
        | EQ, Var a, Var b ->
          SMap.of_seq (List.to_seq [(a, (1, [Var b])); (b, (1, [Var a]))])
        | EQ, Var a, b | EQ, b, Var a ->
          plus (SMap.singleton a (1, [b])) (self#visit_term () b)
        | EQ, a, b -> plus (self#visit_term () a) (self#visit_term () b)
        | _, a, b ->
          plus (self#visit_term () a) (self#visit_term () b)

      method! visit_Var _ v = SMap.singleton v (1, [])

      method! visit_PointsTo _ (v, t) =
        plus (SMap.singleton v (1, [])) (self#visit_term () t)

      (* there can be unnormalized specs inside normalized ones *)
      method! visit_HigherOrder _ ((_p, _h, (f, _a), _r) as fn) =
        plus (SMap.singleton f (1, [])) (super#visit_HigherOrder () fn)

      method! visit_EffHOStage _ eh =
        match eh.e_typ with
        | `Eff -> super#visit_EffHOStage () eh
        | `Fn ->
          plus (SMap.singleton (fst eh.e_constr) (1, []))
            (super#visit_EffHOStage () eh)
    end
  in
  vis


let used_vars (sp : normalisedStagedSpec) =
  count_uses_and_equalities#visit_normalisedStagedSpec () sp |> SMap.key_set

let used_vars_pi p =
  count_uses_and_equalities#visit_pi () p |> SMap.key_set

let used_vars_state (p, h) =
  count_uses_and_equalities#visit_state () (p, h) |> SMap.key_set

let used_vars_eff (eff:effHOTryCatchStages) =
  count_uses_and_equalities#visit_effHOTryCatchStages () eff |> SMap.key_set

let used_vars_norm (norm:normalStage) =
  count_uses_and_equalities#visit_normalStage () norm |> SMap.key_set

let used_vars_disj_spec (norm:disj_spec) =
  count_uses_and_equalities#visit_disj_spec () norm |> SMap.key_set

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

let get_existentials_eff (e : effHOTryCatchStages) : string list =
  match e with
  | EffHOStage eff -> eff.e_evars
  | TryCatchStage tc -> tc.tc_evars

let set_existentials_eff (e : effHOTryCatchStages) vs =
  match e with
  | EffHOStage eff -> EffHOStage { eff with e_evars = vs }
  | TryCatchStage tc -> TryCatchStage { tc with tc_evars = vs }

let rec getExistentialVar (spec : normalisedStagedSpec) : string list =
  let effS, normalS = spec in
  match effS with
  | [] ->
    let ex, _, _ = normalS in
    ex
  | (EffHOStage eff) :: xs -> eff.e_evars @ getExistentialVar (xs, normalS)
  | (TryCatchStage tc)::xs -> tc.tc_evars @ getExistentialVar (xs, normalS)
