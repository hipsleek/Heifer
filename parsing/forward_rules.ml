
open Hipcore
open Hiptypes
open Pretty
open Normalize
include Subst


let concatenateSpecsWithEvent (current:disj_spec) (event:spec) : disj_spec = 
  List.map (fun a -> List.append a event) current

let concatenateEventWithSpecs  (event:spec) (current:disj_spec) : disj_spec = 
  List.map (fun a -> List.append event a ) current


let concatenateSpecsWithSpec (current:disj_spec) (event:disj_spec) :  disj_spec = 
  List.concat_map (fun a -> concatenateSpecsWithEvent current a) event

let rec retrieve_return_value (spec:spec) : term = 
  match spec with 
  | [] -> failwith "retrieve_return_value empty spec"
  | [NormalReturn (pi, _)] -> get_res pi
  | [HigherOrder (_, _, _, retN)]
  | [RaisingEff(_, _, _, retN)] -> retN
  | _ :: xs -> retrieve_return_value xs 

let rec replace_return_value (t:term) (spec:spec) : spec = 
  match spec with 
  | [] -> failwith "replace_return_value empty spec"
  | [HigherOrder (p, h, i, _)] -> [HigherOrder (p, h, i, t)]
  | [NormalReturn (p, h)] -> [NormalReturn (p, h)]
  | [RaisingEff(p, h, i, _)] -> [RaisingEff (p, h, i, t)]
  | s :: ss -> s :: replace_return_value t ss

(** add an equality to v to the end of all disjuncts *)
let constrain_final_res (sp:disj_spec) (v:term) : disj_spec =
  sp |> List.map (fun s ->
    let l = List.length s in
    s |> List.mapi (fun i a -> if i < l-1 then a else
      match a with
      | Exists _ -> a
      | Require (_, _) -> a
      | NormalReturn (p, h) ->
        NormalReturn (And (p, res_eq v), h)
      | HigherOrder (p, k, (c, va), r) ->
        HigherOrder (And (p, Atomic (EQ, r, v)), k, (c, va), r)
      | RaisingEff (p, k, (c, va), r) ->
        RaisingEff (And (p, Atomic (EQ, r, v)), k, (c, va), r)))

(** Environment used for forward verification *)
type fvenv = {
  (* defined methods, may be added to if lambdas are given names *)
  fv_methods : meth_def SMap.t;

  (* definitions of lambda terms (which are opaque to smt),
     added to when lambdas are defined *)
  fv_lambda : meth_def SMap.t;

  (* methods which need to be changed if a lambda is changed, e.g. by substitution *)
  fv_lambda_names : (string * string) list;

  (* proof obligations generated by defining lambdas with specifications.
     we propagate them out instead of checking them immediately to avoid a cyclic dependency with entailment. *)
  fv_lambda_obl : (disj_spec * disj_spec) list;

  (* proof obligations generated by user-supplied match specs *)
  fv_match_obl : (disj_spec * disj_spec) list;
}

let create_fv_env fv_methods = {
  fv_methods;
  fv_lambda = SMap.empty;
  fv_lambda_obl = [];
  fv_match_obl = [];
  fv_lambda_names = [];
}

let retrieveSpecFromEnv (fname: string) (env:fvenv) : (string list * spec list) option = 
  SMap.find_opt fname env.fv_methods
  |> Option.map (fun m -> (m.m_params, Option.get m.m_spec))


let bindFormalNActual (formal: string list) (actual: core_value list) : ((string * core_value) list)= 
  List.map2 (fun a b -> (a, b)) formal actual

let bindNewNames (formal: string list) (actual: string list) : ((string * string) list)= 
  List.map2 (fun a b -> (a, b)) formal actual




  







let rec getExistientalVar (spec:normalisedStagedSpec) : string list = 
  let (effS, normalS) = spec in 
  match effS with 
  | [] -> 
    let (ex, _, _) = normalS in ex 
  | eff :: xs -> 
    eff.e_evars @ getExistientalVar (xs, normalS)




let instantiateExistientalVarSpec   (spec:spec) 
(bindings:((string * string) list)): spec = 
  let normalSpec = normalise_spec spec in 
  normalisedStagedSpec2Spec (instantiateExistientalVar normalSpec bindings)



let isFreshVar str : bool = 
  if String.length str < 1 then false 
  else 
    let a = String.get str 0 in 
    (*let b = String.get str 1 in *)
    if a='f' (*&& b ='f'*) then true else false 

let () = assert (isFreshVar "f10" ==true )
let () = assert (isFreshVar "s10" ==false )

(** substitutes existentials with fresh variables *)
let renamingexistientalVar (specs:disj_spec): disj_spec = 
  List.map (
    fun spec -> 
      let normalSpec = normalise_spec spec in 
      let existientalVar = getExistientalVar normalSpec in 
      let newNames = List.map (fun n -> (verifier_getAfreeVar n)) existientalVar in 
      let newNameTerms = List.map (fun a -> Var a) newNames in 
      let bindings = bindNewNames existientalVar newNames in 
      let temp = instantiateExistientalVar normalSpec bindings in 
      let bindings = bindFormalNActual existientalVar newNameTerms in 
      instantiateSpec bindings (normalisedStagedSpec2Spec temp)
  ) specs

(** substitutes existentials with fresh variables, and the resulting formula has no quantifiers *)
let freshen (specs:disj_spec): disj_spec = 
  renamingexistientalVar specs
  |> List.map (List.filter (function Exists _ -> false | _ -> true))


let instantiate_higher_order_functions fname fn_args (spec:disj_spec) : disj_spec =
  let rec loop (acc:stagedSpec Acc.t list) (ss:spec) =
    match ss with
    | [] -> List.map Acc.to_list acc
    | s :: ss1 ->
      (match s with
      | Exists _ | Require (_, _) | NormalReturn _ | RaisingEff _ ->
        loop (List.map (fun tt -> Acc.add s tt) acc) ss1
      | HigherOrder (p, h, (name, args), ret) ->
        let matching = List.find_map (fun (mname, mspec) ->
          match mspec with
          | Some (mparams, msp) when String.equal mname name && List.length mparams = List.length args ->
          Some (mparams, msp)
          | _ -> None) fn_args
        in
        (match matching with
        | None ->
          loop (List.map (fun tt -> Acc.add s tt) acc) ss1
        | Some (mparams, mspec) ->
          let bs = bindFormalNActual mparams args in
          let instantiated = instantiateSpecList bs (renamingexistientalVar mspec)
            (* replace return value with whatever x was replaced with *)
          in
          let res = acc |> List.concat_map (fun tt ->
            List.map (fun dis -> tt |> Acc.add (NormalReturn (p, h)) |> Acc.add_all dis) instantiated)
          in
          let ret1 = match ret with Var s -> s | _ -> failwith (Format.asprintf "return value of ho %s was not a var" (string_of_term ret)) in
          (* instantiate the return value in the remainder of the input before using it *)
          let ss2 =
            let bs = List.map (fun s -> (ret1, retrieve_return_value s)) instantiated in
            instantiateSpec bs ss1
          in
          loop res ss2))
  in
  (* in acc, order of disjuncts doesn't matter *)
  let res = List.concat_map (fun ss -> loop [Acc.empty] ss) spec in
info ~title:(Format.asprintf "instantiate higher order function: %s" fname) "args: %s\n\n%s\n==>\n%s" (string_of_list (string_of_pair Fun.id (string_of_option (string_of_pair (string_of_list Fun.id) (string_of_list string_of_spec)))) fn_args) (string_of_disj_spec spec) (string_of_disj_spec res);
  res

(** Find the case that handles the effect [label] *)
let lookforHandlingCases ops (label:string) = 
  List.find_map (fun (s, arg, spec) ->
    if String.equal s label then Some (arg, spec) else None) ops

(* let (continueationCxt: ((spec list * string * (string * core_lang) * core_handler_ops) list) ref)  = ref []  *)

let map_state env f xs =
  let r, env =
    List.fold_right (fun c (t, env) ->
      let r, e1 = f c env
      in (r :: t, e1)
    ) xs ([], env)
  in
  r, env

(** Like concat_map, but threads an extra "environment" argument through which can be updated by the function *)
let concat_map_state env f xs =
  let r, env = map_state env f xs in
  List.concat r, env

let%expect_test _ =
  let r, e = (concat_map_state 0 (fun x e -> [x; x * 3], e + 1) [1; 2; 3]) in
  Format.printf "%s %d@." (string_of_list string_of_int r) e;
  [%expect
    {| [1; 3; 2; 6; 3; 9] 3 |}]

let foldl1 f xs =
  match xs with
  | [] -> failwith "foldl1"
  | x :: xs1 ->
    List.fold_left f x xs1

let primitives = ["+"; "-"; "="; "not"; "::"; "&&"; "||"; ">"; "<"; ">="; "<="]

(** given the spec of the scrutinee, symbolically executes it against the handler *)
let rec handling_spec env (scr_spec:normalisedStagedSpec) (h_norm:(string * disj_spec)) (h_ops:(string * string option * disj_spec) list) : spec list * fvenv = 
  (* Format.printf "handling_spec <===== %s@." (string_of_spec (normalisedStagedSpec2Spec scr_spec)); *)
  let (scr_eff_stages, scr_normal) = scr_spec in 
  match scr_eff_stages with 
  | [] ->
    (* the scrutinee's effects have been completely handled, so go into the value case *)
    let (h_val_param, h_val_spec) = h_norm in 

    let current =
      (* Given match 1 with v -> v | effect ..., replace v with 1 in the value case *)
      let (_, _, _) = scr_normal in 
      let bindings = bindFormalNActual [h_val_param] [res_v] in 
      let spec = instantiateSpecList bindings h_val_spec in

      (* the heap state present in the scrutinee also carries forward *)
      let (ex, (p1, h1), (p2, h2)) = scr_normal in 
      let hist = [[Exists ex; Require (p1, h1); NormalReturn (p2, h2)]] in
      concatenateSpecsWithSpec hist spec
    in

    (* Format.printf "handling_spec =====> %s@." (string_of_disj_spec current); *)
    current, env
    
  | x :: xs ->
    (* there is an effect stage x in the scrutinee which may or may not be handled *)
    let perform_ret =
      match x.e_ret with 
      | Var ret -> ret
      | _ -> failwith "effect return is not var"
    in
    let (label, _) = x.e_constr in
    match lookforHandlingCases h_ops label with 
    | None ->
      (* effect x is unhandled. handle the rest of the trace and append it after the unhandled effect. this assumption is sound for deep handlers, as if x is resumed, xs will be handled under this handler. *)
      let r, env = handling_spec env (xs, scr_normal) h_norm h_ops in
      concatenateEventWithSpecs (effectStage2Spec [x]) (r), env

    | Some (effFormalArg, handler_body_spec) ->
      (* effect x is handled by a branch of the form (| _ param -> spec) *)

      (* freshen, as each instance of the handler body should not interfere with previous ones *)
      let handler_body_spec = renamingexistientalVar handler_body_spec in

      (* Format.printf "handler body spec\n%s@." (string_of_disj_spec handler_body_spec); *)

      (* the rest of the trace is now the spec of the continuation *)
      let continuation_spec = normalisedStagedSpec2Spec (xs, scr_normal) in 

      let handled_spec, env =
        (* make use of the handler body spec instead of reanalyzing. for each of its disjuncts, ... *)
        handler_body_spec |> concat_map_state env (fun handler_body env ->
          let (eff_stages, norm_stage) = normalise_spec handler_body in
          (* ... each continue stage should be substituted with the spec for continue *)
          let handled, env = eff_stages |> map_state env (fun h_eff_stage env ->
            match h_eff_stage.e_constr with
            | ("continue", [cont_arg]) ->
              (* freshen, as each resumption of the continue spec results in new existentials *)
              let continue_specs = renamingexistientalVar [continuation_spec] in 
        
              (* Given the following running example:

                match (let r = perform A in perform B) with
                | effect A k -> let q = continue k () in ...
                | ...

                but where the scrutinee and continue are both represented by the specs of those expressions,
              *)
                
              (* replace r with () in the spec of continue *)
              let instantiatedSpecs =
                let bindings = bindFormalNActual [perform_ret] [cont_arg] in 
                instantiateSpecList bindings continue_specs
              in

              (* Format.printf "continue spec\n%s@." (string_of_disj_spec instantiatedSpecs); *)

              (* deeply (recursively) handle the rest of each continuation, to figure out the full effects of this continue. note that this is the place where we indirectly recurse on xs, by making it the spec of continue and recursing on each continue stage. this gives rise to tree recursion in a multishot setting. *)
              let handled_rest, env = 
                instantiatedSpecs |> concat_map_state env (fun c env ->
                  let r, env = handling_spec env (normalise_spec c) h_norm h_ops in
                  r, env)
              in

              (* add an equality between the result of continue and q above (the return term of this stage) *)
              let handled_rest =
                constrain_final_res handled_rest h_eff_stage.e_ret 
              in

              (* ensure heap state present in this part of the scrutinee propagates *)
              let handled_rest =
                let { e_evars; e_pre = (p1, h1); e_post = (p2, h2); _} = h_eff_stage in
                let existing = [Exists e_evars; Require (p1, h1); NormalReturn (p2, h2)] in
                concatenateEventWithSpecs existing handled_rest 
              in
              handled_rest, env
            | _ ->
              (* not a continue stage, so just append without doing anything *)
              [normalisedStagedSpec2Spec ([h_eff_stage], freshNormalStage)], env)
          in
          let handled =
            match handled with
            | [] ->
              (* happens when there are handler branches without continues or other function calls/stages *)
              []
            | _ ->
              (* given the effects of each continue/stage, concat them from left to right *)
              foldl1 concatenateSpecsWithSpec handled
          in
          let norm = normalisedStagedSpec2Spec ([], norm_stage) in
          concatenateSpecsWithEvent handled norm, env)
      in
      let res =
        (* after handling stage/effect x, make sure the heap state associated with it propagates, *)
        let { e_evars; e_constr = (_, arg); e_pre = (p1, h1); e_post = (p2, h2); _ } = x in
        let bindings = 
          match effFormalArg, arg with 
          | _, [] | None, _ -> [] 
          | Some e, effactualArg ::_ -> [(e, effactualArg)]
        in 
        let hist = [Exists e_evars; Require (p1, h1); NormalReturn (p2, h2)] in
        concatenateEventWithSpecs hist (instantiateSpecList bindings handled_spec), env
      in
      (* Format.printf "handling_spec =====> %s@." (string_of_disj_spec (fst res)); *)
      res


 
(** may update the environment because of higher order functions *)
let rec infer_of_expression (env:fvenv) (current:disj_spec) (expr:core_lang): disj_spec * fvenv =
  (* TODO infer_of_expression is likely O(n^2) due to appending at the end *)
  let res, env =
    match expr with
    | CValue v -> 
      let event = NormalReturn (res_eq v, EmptyHeap) in 
      concatenateSpecsWithEvent current [event], env

    | CLet (str, expr1, expr2) ->
      let phi1, env = infer_of_expression env current expr1 in 
      phi1 |> concat_map_state env (fun spec env -> 
        (* Format.printf "lang %s@." (string_of_core_lang expr1); *)
        (* Format.printf "spec %s@." (string_of_spec spec); *)
        let retN = retrieve_return_value spec in 
        match retN with 
        | UNIT ->
          infer_of_expression env [spec] expr2
        (*| Var freshV -> 
          if String.compare str "_" == 0 then infer_of_expression env [spec] expr2
          
          else if String.compare str "i" == 0 || String.compare str "j" == 0  then 
            (
            (*print_endline ("replacing " ^ freshV ^ " with " ^str);
            print_endline ("spec   " ^ string_of_spec spec);*)
            (* instantiate the exist value first *)
            let bindings = bindNewNames [freshV] [str] in 
            let spec' = instantiateExistientalVarSpec spec bindings in 
            (*print_endline ("spec'  " ^ string_of_spec spec');*)
            (* instantiate the terms value first *)
            let bindings = bindFormalNActual [freshV] [Var str] in 
            let spec' = instantiateSpec bindings spec' in 
            (*print_endline ("spec'' " ^ string_of_spec spec'); *)
            (*let spec' = removeExist [spec'] freshV in *)
            infer_of_expression env [spec'] expr2)
          
          else 
            let bindings = bindFormalNActual [str] [retN] in 
            let phi2 = infer_of_expression env [spec] expr2 in 
            instantiateSpecList bindings phi2
            *)
        | _ when String.equal str "_" ->
          infer_of_expression env [spec] expr2
        | _ ->

          (* rather than create an existential, we substitute the new variable away *)
          let bindings = bindFormalNActual [str] [retN] in 

          (* if expr1 is a lambda, copy its binding to the method env before processing expr2 *)
          let env =
            match phi1 with
            | [p] ->
              (match retrieve_return_value p with
              | TLambda (n, _params, _sp) ->
                let lspec = SMap.find n env.fv_lambda in
                (* rename, so created predicate will match *)
                let lspec = { lspec with m_name = str } in
                { env with fv_methods = env.fv_methods |> SMap.add str lspec;
                  fv_lambda_names = (n, str) :: env.fv_lambda_names }
              | _ -> env)
            | _ -> env
          in

          let phi2, env, lambdas_in_expr2 =
            let phi2, env1 = infer_of_expression env [freshNormalReturnSpec] expr2 in
            let ll =
              let prev = SMap.bindings env.fv_lambda |> List.map fst |> SSet.of_list in
              let curr = SMap.bindings env1.fv_lambda |> List.map fst |> SSet.of_list in
              SSet.diff curr prev
            in
            phi2, env1, ll
          in

          (* Here, we only instantiate the expr2 and *)
          let phi2' = instantiateSpecList bindings phi2 in

          (* also substitute inside the specs of lambdas defined in expr2. this has to be done after expr2 is inferred (as then we will know which lambda specs to change), so we need to fix all methods which lambdas have been bound to as well *)
          let env =
            let fv_lambda =
              env.fv_lambda |> SMap.mapi (fun k v -> if SSet.mem k lambdas_in_expr2 then { v with m_spec = Option.map (fun s -> instantiateSpecList bindings s) v.m_spec } else v)
            in
            let fv_methods =
              let methods_to_change =
                env.fv_lambda_names |> List.filter_map (fun (n, m) -> if SSet.mem n lambdas_in_expr2 then Some m else None) |> SSet.of_list
              in
              SMap.mapi (fun k v -> if SSet.mem k methods_to_change then { v with m_spec = Option.map (fun s -> instantiateSpecList bindings s) v.m_spec } else v) env.fv_methods
            in
            { env with fv_lambda; fv_methods }
          in

          (* concat spec -- the spec for expr 1 -- in front *)
          concatenateSpecsWithSpec [spec] phi2', env
        )
    | CRef v -> 
      let freshVar = verifier_getAfreeVar "ref" in 
      let event = NormalReturn (res_eq (Var freshVar), PointsTo(freshVar, v)) in 
      concatenateSpecsWithEvent current [Exists [freshVar];event], env


    | CRead str -> 
      let freshVar = verifier_getAfreeVar str in 
      let event = [Exists [freshVar];Require(True, PointsTo(str, Var freshVar)); 
        NormalReturn (res_eq (Var freshVar), PointsTo(str, Var freshVar))] in 
      concatenateSpecsWithEvent current event, env


    | CAssert (p, h) -> 
      let temp = concatenateSpecsWithEvent current [Require(p, h)] in 
      concatenateSpecsWithEvent temp [(NormalReturn(And (res_eq UNIT, p), h))], env

    | CPerform (label, arg) -> 
          
      let arg = 
        match arg with 
        | Some v -> [v]
        | _ -> []
      in 
      let freshVar = verifier_getAfreeVar "per" in 
      (* after adding the perfome stage, we need to add a normal return. *)
      concatenateSpecsWithEvent current 
      [Exists [freshVar];RaisingEff(True, EmptyHeap, (label,arg), Var freshVar);
      NormalReturn (res_eq (Var freshVar), EmptyHeap)], env


    | CResume v ->  
      let f = verifier_getAfreeVar "re" in
      let res =
        concatenateSpecsWithEvent current [Exists [f]; RaisingEff (True, EmptyHeap, ("continue", [v]), Var f)]
      in
      res, env
    | CFunCall (fname, actualArgs) -> 
      (match List.mem fname primitives with
      | true ->
        (match fname, actualArgs with
        | "+", [x1; x2] ->
          let event = NormalReturn (res_eq (Plus(x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | "-", [x1; x2] ->
          let event = NormalReturn (res_eq (Minus(x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | "=", [x1; x2] ->
          (* let event = NormalReturn (Atomic (EQ, x1, x2), EmptyHeap, Eq (x1, x2)) in *)
          let event = NormalReturn (res_eq (Rel (EQ, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | "not", [x1] ->
          let event = NormalReturn (res_eq (TNot (x1)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | "&&", [x1; x2] ->
          let event = NormalReturn (res_eq (TAnd (x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | "||", [x1; x2] ->
          let event = NormalReturn (res_eq (TOr (x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | ">", [x1; x2] ->
          let event = NormalReturn (res_eq (Rel (GT, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | "<", [x1; x2] ->
          let event = NormalReturn (res_eq (Rel (LT, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | ">=", [x1; x2] ->
          let event = NormalReturn (res_eq (Rel (GTEQ, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | "<=", [x1; x2] ->
          let event = NormalReturn (res_eq (Rel (LTEQ, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | "::", [x1; x2] ->
          let event = NormalReturn (res_eq (TApp ("cons", [x1; x2])), EmptyHeap) in
          concatenateSpecsWithEvent current [event], env
        | _ -> failwith (Format.asprintf "unknown primitive: %s, args: %s" fname (string_of_list string_of_term actualArgs)))
      | false ->
        let spec_of_fname =
          (match retrieveSpecFromEnv fname env with 
          | None ->
            let ret = verifier_getAfreeVar "ret" in
            [[Exists [ret]; HigherOrder (True, EmptyHeap, (fname, actualArgs), Var ret)]]
          | Some (formalArgs, spec_of_fname) -> 
            (* TODO should we keep existentials? *)
            let spec = renamingexistientalVar spec_of_fname in
            (* let spec = freshen spec_of_fname in *)
            (* Format.printf "after freshen: %s@." (string_of_disj_spec spec); *)
            if List.compare_lengths formalArgs actualArgs <> 0 then
              failwith (Format.asprintf "too few args. formals: %s, actual: %s@." (string_of_list Fun.id formalArgs) (string_of_list string_of_term actualArgs));
            let spec =
              (* we've encountered a function call, e.g. f x y.
                we look up the spec for f. say it looks like:
                  let f g h (*@ g$(...); ... @*) = ...
                we now want to instantiate g with the spec for x. *)
              let fnArgs = List.map2 (fun p x ->
                match x with
                | Var a ->
                  (p, retrieveSpecFromEnv a env)
                | TLambda _ ->
                  (* if a is a lambda, get its spec here *)
                  failwith "lambda case not implemented"
                | _ -> (p, None)
                ) formalArgs actualArgs
              in
              (* fnArgs is a map of g -> spec, h -> none, assuming h is not a functino *)
              instantiate_higher_order_functions fname fnArgs spec
            in
            (* Format.printf "after ho fns: %s@." (string_of_disj_spec spec); *)
            let bindings = bindFormalNActual (formalArgs) (actualArgs) in 
            let instantiatedSpec = instantiateSpecList bindings spec in 
            instantiatedSpec)
            (*print_endline ("====\n"^ string_of_spec_list spec_of_fname);*)
        in
        let _spec_of_fname =
          (* this is an alternative implementation for this whole case, which simply generates an uninterpreted function and lets the entailment procedure take care of unfolding (since the implementation above can be seen as unfolding once). unfortunately the handler reasoning in the effects work relies on unfolding in the forward reasoning, so we can't switch to it yet, but this implementation should work for higher-order *)
          let ret = verifier_getAfreeVar "ret" in
          [[Exists [ret]; HigherOrder (True, EmptyHeap, (fname, actualArgs), Var ret); NormalReturn (res_eq (Var ret), EmptyHeap)]]
        in
        concatenateSpecsWithSpec current spec_of_fname, env)
    | CWrite  (str, v) -> 
      let freshVar = verifier_getAfreeVar "wr" in 
      let event = [Exists [freshVar];Require(True, PointsTo(str, Var freshVar)); 
                    NormalReturn (res_eq UNIT, PointsTo(str, v))] in 
      concatenateSpecsWithEvent current event, env


    | CIfELse (v, expr2, expr3) -> 
      let eventThen = NormalReturn (Atomic (EQ, v, TTrue), EmptyHeap) in 
      let eventElse = NormalReturn (Not (Atomic (EQ, v, TTrue)), EmptyHeap) in 
      let currentThen = concatenateSpecsWithEvent current [eventThen] in 
      let currentElse = concatenateSpecsWithEvent current [eventElse] in 
      let r1, env = infer_of_expression env currentThen expr2 in
      let r2, env = infer_of_expression env currentElse expr3 in
      r1 @ r2, env


    | CLambda (params, given_spec, body) ->
      let inferred, env = infer_of_expression env [[]] body in
      let inferred = inferred |> List.map (fun s -> s |> normalise_spec |> normalisedStagedSpec2Spec) in
      let lid = verifier_getAfreeVar "lambda" in
      debug ~at:2 ~title:(Format.asprintf "lambda spec %s" lid) "%s" (string_of_disj_spec inferred);
      let mdef = {
        m_name = lid;
        m_params = params; (* TODO unit param? *)
        m_spec = Some inferred; (* TODO given? *)
        m_body = body;
        m_tactics = [];
      } in
      let env = { env with fv_lambda = SMap.add lid mdef env.fv_lambda } in
      let env =
        match given_spec with
        | None -> env
        | Some g -> { env with fv_lambda_obl = (inferred, g) :: env.fv_lambda_obl }
      in
      (* TODO given *)
      let event = NormalReturn (res_eq (TLambda (lid, params, inferred)), EmptyHeap) in 
      concatenateSpecsWithEvent current [event], env

    | CMatch (scr, Some val_case, eff_cases, []) -> (* effects *)
      (* infer specs for branches of the form (Constr param -> spec), which also updates the env with obligations *)
      let inferred_branch_specs, env =
        List.fold_right (fun (effname, param, spec, body) (t, env) ->
          let r, env = infer_of_expression env [[]] body in
          let env, sp =
            match spec with
            | None -> env, r
            | Some s -> { env with fv_match_obl = (r, s) :: env.fv_match_obl }, s
          in
          (effname, param, sp) :: t, env
        ) eff_cases ([], env)
      in
      let inferred_val_case, env =
        let (param, body)  = val_case in
        let inf_val_spec, env = infer_of_expression env [[]] body in
        (param, inf_val_spec), env
      in
      (* for each disjunct of the scrutinee's behaviour, reason using the handler *)
      let phi1, env = infer_of_expression env [freshNormalReturnSpec] scr in 
      let afterHandling, env =
        concat_map_state env (fun spec env -> 
          handling_spec env (normalise_spec spec) inferred_val_case inferred_branch_specs
        ) phi1
      in 
      let res, env = concatenateSpecsWithSpec current afterHandling, env in
      res, env
    | CMatch (discr, None, _, cases) -> (* pattern matching *)
      (* this is quite similar to if-else. generate a disjunct for each branch with variables bound to the result of destructuring *)
      let dsp, env = infer_of_expression env current discr in
      let dsp, env = dsp |> concat_map_state env (fun sp env ->
        let ret = retrieve_return_value sp in
        cases |> concat_map_state env (fun (constr, vars, body) env -> 
          (* TODO this is hardcoded for lists for now *)
          match constr, vars with
          | "[]", [] ->
            let nil_case =
              let c = conj [Atomic (EQ, TApp ("is_nil", [ret]), TTrue)] in
              [NormalReturn (c, EmptyHeap)]
            in 
            infer_of_expression env (concatenateSpecsWithEvent current nil_case) body
          | "::", [v1; v2] ->
            let cons_case =
              let c = conj [
                Atomic (EQ, TApp ("is_cons", [ret]), TTrue);
                Atomic (EQ, TApp ("head", [ret]), Var v1);
                Atomic (EQ, TApp ("tail", [ret]), Var v2);
              ] in
              [Exists [v1; v2]; NormalReturn (c, EmptyHeap)]
            in
            infer_of_expression env (concatenateSpecsWithEvent current cons_case) body
          | _ -> failwith (Format.asprintf "unknown constructor: %s" constr)))
      in
      dsp, env
    | CMatch (_, Some _, _, _ :: _) ->
      (* TODO *)
      failwith "combining effect handlers and pattern matching not yet unimplemented"
  in
  debug ~at:3 ~title:"forward rules" "{%s}\n%s\n{%s}" (string_of_disj_spec current) (string_of_core_lang expr) (string_of_disj_spec res);
  res, env
