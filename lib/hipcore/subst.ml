open Hiptypes


let subst_free_vars =
  let rec findbinding str vb_li =
    match vb_li with
    | [] -> Var str
    | (name, v) :: xs ->
      if String.compare name str == 0 then v else findbinding str xs
  in
  let subst_visitor =
    object (self)
      inherit [_] map_spec

      method! visit_Shift bindings nz k body =
        (* shift binds k *)
        let bs = List.filter (fun (b, _) -> (b <> k)) bindings in
        Shift (nz, k, self#visit_staged_spec bs body)

      method! visit_Exists bindings x f =
        let bs = List.filter (fun (b, _) -> (b <> x)) bindings in
        Exists (x, self#visit_staged_spec bs f)

      (* not full capture-avoiding, we just stop substituting a name when it is bound *)
      method! visit_TLambda bindings name params sp body =
        let bs = List.filter (fun (b, _) -> not (List.mem b params)) bindings in
        TLambda (name, params, (Option.map (self#visit_staged_spec bs) sp), (self#visit_option self#visit_core_lang bs body))

      method! visit_CLambda bindings params sp body =
        let bs = List.filter (fun (b, _) -> not (List.mem b params)) bindings in
        (* Format.printf "bs: %s@." (string_of_list (string_of_pair Fun.id string_of_term) bs); *)
        CLambda (params, (self#visit_option self#visit_staged_spec bs sp), (self#visit_core_lang bs body))

      method! visit_Var bindings v =
        let binding = findbinding v bindings in
        (* Format.printf "replacing %s with %s under %s.@." v (string_of_term binding) (string_of_list (string_of_pair Fun.id string_of_term) bindings); *)
        binding
      end
    in fun bs f-> subst_visitor#visit_staged_spec bs f


let free_vars =
  let subst_visitor =
    object (_)
      inherit [_] reduce_spec as super
      method zero = SSet.empty
      method plus = SSet.union

      method! visit_Exists () x f =
        let b = super#visit_Exists () x f in
        SSet.remove x b

      method! visit_TLambda () h ps sp b =
        let b = super#visit_TLambda () h ps sp b in
        List.fold_right (fun c t -> SSet.remove c t) ps b

      method! visit_Bind () x f1 f2 =
        let b = super#visit_Bind () x f1 f2 in
        SSet.remove x b

      method! visit_Var () x =
        SSet.singleton x
      end
    in fun f -> subst_visitor#visit_staged_spec () f

    (* method! visit_PointsTo bindings (str, t1) =
      let binding = findbinding str bindings in
      let newName = match binding with Var str1 -> str1 | _ -> str in
      PointsTo (newName, self#visit_term bindings t1) *)

    (* method! visit_HigherOrder bindings (pi, kappa, (str, basic_t_list), ret) =
      let constr =
        match List.assoc_opt str bindings with Some (Var s) -> s | _ -> str
      in
      HigherOrder
        ( self#visit_pi bindings pi,
          self#visit_kappa bindings kappa,
          (constr, List.map (fun bt -> self#visit_term bindings bt) basic_t_list),
          self#visit_term bindings ret ) *)

    (* method! visit_effectStage bindings effectStage =
      match effectStage.e_typ with
      | `Eff ->
        {
          effectStage with
          e_constr =
            (let (e, a) = effectStage.e_constr in
            (e, List.map (self#visit_term bindings) a));
          e_pre = self#visit_state bindings effectStage.e_pre;
          e_post = self#visit_state bindings effectStage.e_post;
          e_ret = self#visit_term bindings effectStage.e_ret
        }
      | `Fn ->
        let f =
          let f = fst effectStage.e_constr in
          match List.assoc_opt f bindings with Some (Var s) -> s | _ -> f
        in
        { effectStage with
          e_pre = self#visit_state bindings effectStage.e_pre;
          e_post = self#visit_state bindings effectStage.e_post;
          e_constr = (f, List.map (fun bt -> self#visit_term bindings bt) (snd effectStage.e_constr));
          e_ret = self#visit_term bindings effectStage.e_ret
        } *)

    (* TODO some other expressions like assign and perform need to be implemented *)

    (* method! visit_CFunCall bindings f args =
      let f1 = findbinding f bindings in
      match f1 with
      | Var s -> CFunCall (s, args)
      | _ ->
        let s = verifier_getAfreeVar "x" in
        CLet (s, CValue f1, CFunCall (s, args)) *)

  (* end *)

(*

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

  | (ShiftStage sh) :: xs ->
    let rest, norm' = instantiateExistientalVar (xs, normalS) bindings in
    ( ShiftStage { sh with s_evars = instantiateExistientalVar_aux sh.s_evars bindings }
      :: rest,
      norm' )

  | (TryCatchStage tc) :: xs ->
    let rest, norm' = instantiateExistientalVar (xs, normalS) bindings in
    ( TryCatchStage { tc with tc_evars = instantiateExistientalVar_aux tc.tc_evars bindings }
      :: rest,
      norm' )

  | (ResetStage rs) :: xs ->
    let rest, norm' = instantiateExistientalVar (xs, normalS) bindings in
    ( ResetStage { rs with rs_evars = instantiateExistientalVar_aux rs.rs_evars bindings }
      :: rest,
      norm' )



  let subst_visitor_subsumptions_only bindings =
    object
      inherit [_] map_spec

      method! visit_Subsumption () a b =
        Subsumption (subst_visitor#visit_term bindings a, subst_visitor#visit_term bindings b)
    end


let instantiateTerms (bindings : (string * core_value) list) (t : term) :
    term =
  subst_visitor#visit_term bindings t

let string_of_bindings bs =
  String.concat "" (List.map (fun (s, t) -> Format.asprintf "[%s/%s]" (string_of_term t) s) bs)

let instantiateSpecList (bindings : (string * core_value) list) (t : disj_spec) : disj_spec =
  let r = subst_visitor#visit_disj_spec bindings t in
  Debug.debug ~at:5
    ~title:"instantiateSpecList"
    "%s\n%s\n%s" (string_of_disj_spec t)
    (string_of_bindings bindings)
    (string_of_disj_spec r);
  r

let instantiateSpec (bindings : (string * core_value) list) (t : spec) : spec =
  let r = subst_visitor#visit_spec bindings t in
  Debug.debug ~at:5
    ~title:"instantiateSpec"
    "%s\n%s\n%s" (string_of_spec t)
    (string_of_bindings bindings)
    (string_of_spec r);
  r

let instantiate_state (bindings : (string * core_value) list) (t : state) : state =
  subst_visitor#visit_state bindings t

let instantiatePure (bindings : (string * core_value) list) (t : pi) :
    pi =
  subst_visitor#visit_pi bindings t

let instantiateHeap (bindings : (string * core_value) list) (t : kappa) :
    kappa =
  subst_visitor#visit_kappa bindings t

let instantiateStages (bindings : (string * core_value) list) (t : stagedSpec) : stagedSpec =
  subst_visitor#visit_stagedSpec bindings t

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
  | TLambda (_id, _params, spec, _body) ->
    let bs = List.mapi (fun i p -> (p, "l" ^ string_of_int i)) (SSet.to_list (used_vars_disj_spec spec)) in
    let renamed =
      instantiateSpecList (List.map (fun (p, v) -> (p, Var v)) bs) spec
    in
    (* don't include body in hash *)
    let n = (List.map snd bs, renamed) in
    (* Format.printf "renamed %s@." (string_of_term n); *)
    Hashtbl.hash n
  | _ -> failwith (Format.asprintf "not a lambda: %s" "(cannot print)")

let get_existentials_eff (e : effHOTryCatchStages) : string list =
  match e with
  | ResetStage rs -> rs.rs_evars
  | EffHOStage eff -> eff.e_evars
  | ShiftStage sh -> sh.s_evars
  | TryCatchStage tc -> tc.tc_evars

let set_existentials_eff (e : effHOTryCatchStages) vs =
  match e with
  | EffHOStage eff -> EffHOStage { eff with e_evars = vs }
  | ShiftStage sh -> ShiftStage { sh with s_evars = vs }
  | TryCatchStage tc -> TryCatchStage { tc with tc_evars = vs }
  | ResetStage rs -> ResetStage { rs with rs_evars = vs }

let rec getExistentialVar (spec : normalisedStagedSpec) : string list =
  let effS, normalS = spec in
  match effS with
  | [] ->
    let ex, _, _ = normalS in
    ex
  | (EffHOStage eff) :: xs -> eff.e_evars @ getExistentialVar (xs, normalS)
  | (ShiftStage sh) :: xs -> sh.s_evars @ getExistentialVar (xs, normalS)
  | (TryCatchStage tc)::xs -> tc.tc_evars @ getExistentialVar (xs, normalS)
  | (ResetStage rs)::xs -> rs.rs_evars @ getExistentialVar (xs, normalS)


  let find_function_stages =
    object
      inherit [_] reduce_normalised
      method zero = []
      method plus = (@)
      method! visit_HigherOrder () (_p, _h, (f, _a), _r) = [f]
      method! visit_EffHOStage () effStage =
        match effStage.e_typ with
        | `Fn -> [fst effStage.e_constr]
        | `Eff -> []

      (* don't go into these for now *)
      method! visit_TLambda () _ _ _ _ = []
      method! visit_Shift () _ _ _ _ = []
      method! visit_Reset () _ _ = []
    end

  let find_subsumptions =
    object
      inherit [_] reduce_spec
      method zero = []
      method plus = (@)
      method! visit_Subsumption () a b = [(a, b)]
    end
*)

let find_equalities =
  object
    inherit [_] reduce_spec
    method zero = []
    method plus = (@)
    method! visit_Atomic () op a b =
      match op with
      | EQ -> [(a, b)]
      | _ -> []
  end

(*
let remove_equalities eqs =
  object
    inherit [_] map_spec
    method! visit_Atomic () op a b =
      match op, a, b with
      | EQ, a, b when List.mem (a, b) eqs -> True
      | _ ->
        Atomic (op, a, b)
  end

let remove_subsumptions subs =
  object
    inherit [_] map_spec
    method! visit_Subsumption () a b =
      if List.mem (a, b) subs then True else Subsumption (a, b)
  end
*)

let needs_why3 =
  object
    inherit [_] reduce_spec
    method zero = false
    method plus = (||)

    method! visit_TApp () _f _a =
      true
  end

(*
let quantify_res p =
  let r, rez = split_res_fml p in
  let nv = verifier_getAfreeVar "split" in
  And (r, instantiatePure ["res", Var nv] rez), nv

(** existentially quantify, i.e. replace with fresh variable *)
let quantify_res_state (p, h) =
  let p1, nv = quantify_res p in
  (p1, h), nv

  let contains_res_state (p, h) =
    SSet.mem "res" (used_vars_state (p, h))
*)
