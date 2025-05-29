open Hiptypes
open Typedhip
open Pretty_typed

let find_new_mapping elem assoc =
  List.assoc_opt elem assoc |> Option.value ~default:elem

let findNewName str vb_li = find_new_mapping str vb_li

let instantiateExistientalVar_aux li bindings =
  List.map (fun s -> findNewName s bindings) li

(** Rename a list of variables in a normalized specification. *)
let rec instantiateExistientalVar (spec : normalisedStagedSpec)
    (bindings : (binder * binder) list) : normalisedStagedSpec =
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


let findbinding str vb_li =
  List.assoc_opt (ident_of_binder str) vb_li |> Option.value ~default:(var_from_binder str)

(** Object with several visitor methods that replace all instances
    of a free variable with a given term. 

    The identifiers used for bindings are untyped because this visitor is also used to rename
    things that aren't exactly binders (e.g. identifiers for higher-order functions/effect constructors). *)
  let subst_visitor =
    object (self)
      inherit [_] map_normalised as super

      method! visit_Shift (bindings : (string * term) list) nz k body ret =
        (* shift binds res and k *)
        let bs = List.filter (fun (b, _) -> not (List.mem b [(ident_of_binder k); "res"])) bindings in
        Shift (nz, k, self#visit_disj_spec bs body, self#visit_term bs ret)

      (* not full capture-avoiding, we just stop substituting a name when it is bound *)
      method! visit_TLambda bindings name params sp body =
        let bs = List.filter (fun (b, _) -> not (List.mem b (List.map ident_of_binder params))) bindings in
        TLambda (name, params, (self#visit_disj_spec bs sp), (self#visit_option self#visit_core_lang bs body))

      method! visit_CLambda bindings params sp body =
        let bs = List.filter (fun (b, _) -> not (List.mem b (List.map ident_of_binder params))) bindings in
        Format.printf "bs: %s@." (string_of_list (string_of_pair Fun.id string_of_term) bs);
        CLambda (params, (self#visit_option self#visit_disj_spec bs sp), (self#visit_core_lang bs body))

      method! visit_Exists _ v = Exists v

      method! visit_PointsTo bindings (str, t1) =
        let binding = findbinding (binder_of_ident str) bindings in
        let newName = match binding.term_desc with Var str1 -> str1 | _ -> str in
        PointsTo (newName, self#visit_term bindings t1)

      method! visit_HigherOrder bindings (pi, kappa, (str, basic_t_list), ret) =
        let constr =
          match List.assoc_opt str bindings with Some {term_desc = Var s; _}-> s | _ -> str
        in
        HigherOrder
          ( self#visit_pi bindings pi,
            self#visit_kappa bindings kappa,
            (constr, List.map (fun bt -> self#visit_term bindings bt) basic_t_list),
            self#visit_term bindings ret )

      method! visit_effectStage bindings effectStage =
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
            match List.assoc_opt f bindings with Some {term_desc = Var s; _} -> s | _ -> f
          in
          { effectStage with
            e_pre = self#visit_state bindings effectStage.e_pre;
            e_post = self#visit_state bindings effectStage.e_post;
            e_constr = (f, List.map (fun bt -> self#visit_term bindings bt) (snd effectStage.e_constr));
            e_ret = self#visit_term bindings effectStage.e_ret
          }

      (* TODO some other expressions like assign and perform need to be implemented *)

      (* visitor methods that need the enclosing node's type *)

      method! visit_core_lang bindings cl =
        match cl.core_desc with
        | CFunCall (f, args) ->
          let f1 = findbinding (binder_of_ident f) bindings in
          begin match f1 with
          (* if bound to a variable, simply rename the function call *)
          | {term_desc = Var s; _} -> {cl with core_desc = CFunCall (s, args)}
          (* otherwise, use a let-binding to capture the value *)
          | _ ->
            let s = verifier_getAfreeVar "x" in
            {cl with core_desc = CLet (ident_of_binder s, {core_desc = CValue f1; core_type = f1.term_type}, {core_desc = CFunCall (ident_of_binder s, args); core_type = cl.core_type})}
          end
        | _ -> super#visit_core_lang bindings cl

      method! visit_term bindings t =
        match t.term_desc with
        | Var _ ->
            findbinding (binder_of_var t) bindings
        | _ -> super#visit_term bindings t
    end

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

      method! visit_Atomic _ op lhs rhs =
        match op, lhs, rhs with
        | EQ, {term_desc = Var a; _}, {term_desc = Var b; _} ->
          SMap.of_seq (List.to_seq [(a, (1, [rhs])); (b, (1, [lhs]))])
        | EQ, {term_desc = Var a; _}, b | EQ, b, {term_desc = Var a; _} ->
          plus (SMap.singleton a (1, [rhs])) (self#visit_term () b)
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
  match t.term_desc with
  | TLambda (_id, _params, spec, _body) ->
    let bs = List.mapi (fun i p -> (p, "l" ^ string_of_int i)) (SSet.to_list (used_vars_disj_spec spec)) in
    let renamed =
      (* this destroys a good amount of type information, but is only needed so two alpha-equivalent
         lambdas get hashed to the same value, so it's fine *)
      instantiateSpecList (List.map (fun (p, v) -> (p, var_from_binder (binder_of_ident v))) bs) spec
    in
    (* don't include body in hash *)
    let n = (List.map snd bs, renamed) in
    (* Format.printf "renamed %s@." (string_of_term n); *)
    Hashtbl.hash n
  | _ -> failwith (Format.asprintf "not a lambda: %s" "(cannot print)")

let get_existentials_eff (e : effHOTryCatchStages) : binder list =
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

let rec getExistentialVar (spec : normalisedStagedSpec) : binder list =
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

  let find_equalities =
    object
      inherit [_] reduce_normalised
      method zero = []
      method plus = (@)
      method! visit_Atomic () op a b =
        match op with
        | EQ -> [(a, b)]
        | _ -> []
    end

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

let rec interpret_arrow_as_params t =
  match t with
  | Arrow (t1, t2) ->
    let p, r = interpret_arrow_as_params t2 in
    t1 :: p, r
  | _ -> [], t

let get_type_of_free_var ident pi =
  let visitor =
    object
      inherit [_] reduce_normalised as super
      method zero = []
      method plus = (@)

      method! visit_term ident t =
        match t.term_desc with
        | Var name when name = ident ->
            [t.term_type]
        | _ -> super#visit_term ident t
    end in
  
  (* TODO: make this more robust by checking for the "most concrete type"/failing on type mismatch *)
  visitor#visit_pi ident pi |> List.hd

let quantify_res p =
  let r, rez = split_res_fml p in
  let nv = verifier_getAfreeVar ~typ:(get_type_of_free_var "res" p) "split" in
  And (r, instantiatePure ["res", var_from_binder nv] rez), nv

(** existentially quantify, i.e. replace with fresh variable *)
let quantify_res_state (p, h) =
  let p1, nv = quantify_res p in
  (p1, h), nv

  let contains_res_state (p, h) =
    SSet.mem "res" (used_vars_state (p, h))

let needs_why3 =
  object
    inherit [_] reduce_spec
    method zero = false
    method plus = (||)

    method! visit_TApp () _f _a =
      true
  end
