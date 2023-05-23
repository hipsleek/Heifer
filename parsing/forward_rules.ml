
open Hiptypes
open Pretty

let rec findbinding str vb_li =
    match vb_li with 
    | [] -> Var str 
    | (name, v) :: xs -> if String.compare name str == 0 then v else  findbinding str xs


let concatenateSpecsWithEvent (current:spec list) (event:stagedSpec list) :  spec list = 
  List.map (fun a -> List.append a event) current

let concatenateEventWithSpecs  (event:spec) (current:spec list) :  spec list = 
  List.map (fun a -> List.append event a ) current


let concatenateSpecsWithSpec (current:spec list) (event:spec list) :  spec list = 
  let temp  = List.map (fun a -> concatenateSpecsWithEvent current a) event in 
  List.flatten temp

let rec retrieve_return_value (spec:spec) : term = 
  match spec with 
  | [] -> failwith "retrieve_return_value empty spec"
  | [HigherOrder (_, _, _, retN)] 
  | [NormalReturn (_, _, retN)] 
  | [RaisingEff(_, _, _, retN)] -> retN
  | _ :: xs -> retrieve_return_value xs 

let rec replace_return_value (t:term) (spec:spec) : spec = 
  match spec with 
  | [] -> failwith "replace_return_value empty spec"
  | [HigherOrder (p, h, i, _)] -> [HigherOrder (p, h, i, t)]
  | [NormalReturn (p, h, _)] -> [NormalReturn (p, h, t)]
  | [RaisingEff(p, h, i, _)] -> [RaisingEff (p, h, i, t)]
  | s :: ss -> s :: replace_return_value t ss

let (*rec*) retrieveSpecFromEnv (fname: string) (env:meth_def list) : (string list * spec list) option = 
  (* match env with 
  | [] -> None 
  | m :: xs ->  
    if String.compare fname m.m_name == 0 then Some (m.m_params, m.m_spec) 
    else retriveSpecFromEnv fname xs *)
  List.find_map (fun m -> if String.equal fname m.m_name then Some (m.m_params, m.m_spec) else None) env


let (*rec*) bindFormalNActual (formal: string list) (actual: core_value list) : ((string * core_value) list)= 
  (* match (formal, actual) with 
  | ([], []) -> []
  | (x::xs , y::ys) -> (x, y) :: bindFormalNActual xs ys
  | ( _,  _ ) -> failwith "bindFormalNActual different lenth arguments" *)
  List.map2 (fun a b -> (a, b)) formal actual

let (*rec*) bindNewNames (formal: string list) (actual: string list) : ((string * string) list)= 
  (* match (formal, actual) with 
  | ([], []) -> []
  | (x::xs , y::ys) -> (x, y) :: bindNewNames xs ys
  | ( _,  _ ) -> failwith "bindNewNames different lenth arguments" *)
  List.map2 (fun a b -> (a, b)) formal actual




  


let rec instantiateTerms (bindings:((string * core_value) list)) (t:term) : term = 
  match t with
  | Num _ 
  | UNIT -> t
  | Var str -> 
    let binding = findbinding str bindings in 
    binding

  | TList (tLi) -> TList (List.map (fun t1 -> instantiateTerms bindings t1) tLi)
  | TTupple (tLi) -> TList (List.map (fun t1 -> instantiateTerms bindings t1) tLi)
  | Plus (t1, t2) -> Plus (instantiateTerms bindings t1, instantiateTerms bindings t2)
  | Minus (t1, t2) -> Minus (instantiateTerms bindings t1, instantiateTerms bindings t2)



let rec instantiatePure (bindings:((string * core_value) list)) (pi:pi) : pi = 
  match pi with
  | True
  | False -> pi
  | Atomic (bop, t1, t2) -> Atomic (bop, instantiateTerms bindings t1, instantiateTerms bindings t2)
  | And    (p1, p2) -> And (instantiatePure bindings p1, instantiatePure bindings p2)
  | Or     (p1, p2) -> Or (instantiatePure bindings p1, instantiatePure bindings p2)
  | Imply  (p1, p2) -> Imply (instantiatePure bindings p1, instantiatePure bindings p2)
  | Not    p1 -> Not (instantiatePure bindings p1)
  | Predicate (str, t1) -> Predicate(str, instantiateTerms bindings t1)

let rec instantiateHeap (bindings:((string * core_value) list)) (kappa:kappa) : kappa = 
  match kappa with 
  | EmptyHeap -> kappa
  | PointsTo (str, t1) -> 
    let binding = findbinding str bindings in 
    let newName = (match binding with 
    | Var str1 -> str1
    | _ -> str
    ) in 
    PointsTo (newName, instantiateTerms bindings t1)

  | SepConj (k1, k2) -> SepConj (instantiateHeap bindings k1, instantiateHeap bindings k2)




let instantiateStages (bindings:((string * core_value) list))  (stagedSpec:stagedSpec) : stagedSpec = 
  match stagedSpec with 
  | Exists _ -> stagedSpec
  | Require (pi, kappa) -> 
    Require (instantiatePure bindings pi, instantiateHeap bindings  kappa)
  (* higher-order functions *)
  | NormalReturn (pi, kappa, ret) -> 
    NormalReturn(instantiatePure bindings pi, instantiateHeap bindings kappa, instantiateTerms bindings ret) 
  | HigherOrder (pi, kappa, (str, basic_t_list), ret) -> 
    HigherOrder (instantiatePure bindings pi, instantiateHeap bindings kappa, (str, List.map (fun bt -> instantiateTerms bindings bt) basic_t_list), instantiateTerms bindings ret)
  (* effects *)
  | RaisingEff (pi, kappa, (label, basic_t_list), ret)  -> 
    RaisingEff (instantiatePure bindings pi, instantiateHeap bindings  kappa, (label, 
    List.map (fun bt -> instantiateTerms bindings bt) basic_t_list
    ), instantiateTerms bindings ret) 
  (* | Pred {name; args}  ->  *)
    (* Pred {name; args = List.map (instantiateTerms bindings) args} *)



let instantiateSpec (bindings:((string * core_value) list)) (sepc:spec) : spec =
  List.map (fun a -> instantiateStages bindings a ) sepc

let instantiateSpecList (bindings:((string * core_value) list)) (sepcs:disj_spec) : disj_spec =
  List.map (fun a -> instantiateSpec bindings a ) sepcs


let rec getExistientalVar (spec:normalisedStagedSpec) : string list = 
  let (effS, normalS) = spec in 
  match effS with 
  | [] -> 
    let (ex, _, _, _) = normalS in ex 
  | eff :: xs -> 
    eff.e_evars @ getExistientalVar (xs, normalS)


let rec findNewName str vb_li =
    match vb_li with 
    | [] -> str 
    | (name, new_name) :: xs -> if String.compare name str == 0 then new_name else  findNewName str xs



let rec instantiateExistientalVar_aux (li:string list)   (bindings:((string * string) list)) : string list = 
  match li with 
  | [] -> []
  | str :: xs  -> 
    let str' = findNewName  str bindings in 
    str' :: instantiateExistientalVar_aux xs bindings


let rec instantiateExistientalVar 
  (spec:normalisedStagedSpec) 
  (bindings:((string * string) list)): normalisedStagedSpec = 

  let (effS, normalS)  =  spec  in 
  match effS with 
  | [] -> 
    let (ex, req, ens, ret) = normalS in 
    ([], (instantiateExistientalVar_aux ex bindings, req, ens, ret))
  | eff :: xs -> 
    let (rest, norm') = instantiateExistientalVar (xs, normalS) bindings in 
    (({eff with e_evars = instantiateExistientalVar_aux eff.e_evars bindings}) :: rest, norm')


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
let renamingexistientalVar (specs:spec list): spec list = 
  List.map (
    fun spec -> 
      let normalSpec = normalise_spec spec in 
      let existientalVar = getExistientalVar normalSpec in 
      let newNames = List.map (fun n -> (verifier_getAfreeVar ~from:n ())) existientalVar in 
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


let instantiate_higher_order_functions fn_args (spec:disj_spec) : disj_spec =
  List.concat_map (fun ss ->
    let rec loop (acc:disj_spec) (ss:spec) =
      match ss with
      | [] -> List.map List.rev acc
      | s :: ss1 ->
        begin match s with
        | Exists _ | Require (_, _)
        | NormalReturn _ | RaisingEff _ ->
          loop (List.map (fun tt -> s :: tt) acc) ss1
        | HigherOrder (_p, _h, (name, args), ret) ->
          let matching = List.find_map (fun (mname, mspec) ->
            match mspec with
            | Some (mparams, msp) when String.equal mname name && List.length mparams = List.length args ->
            Some (mparams, msp)
            | _ -> None) fn_args in
          begin match matching with
          | None ->
            loop (List.map (fun tt -> s :: tt) acc) ss1
          | Some (mparams, mspec) ->
            let bs = bindFormalNActual mparams args in
            let instantiated = instantiateSpecList bs (renamingexistientalVar mspec)
              (* replace return value with whatever x was replaced with *)
            in
            (* reversed because we're really adding in reverse to each element of the outer list - the ordering of the (set of) disjuncts doesn't matter *)
            let res = List.concat_map (fun tt ->
              List.map (fun dis -> List.rev dis @ tt) instantiated) acc in
            let ret1 = match ret with Var s -> s | _ -> failwith (Format.asprintf "return value of ho %s was not a var" (string_of_term ret)) in
            (* instantiate the return value in the remainder of the input before using it *)
            let ss2 =
              let bs = List.map (fun s -> (ret1, retrieve_return_value s)) instantiated in
              instantiateSpec bs ss1
            in
            loop res ss2
          end
        end
    in
    loop [[]] ss
  ) spec


let rec lookforHandlingCases ops (label:string) = 
  match ops with 
  | [] -> None
  | (str, arg, expr)::xs -> 
    if String.compare label str == 0 
    then Some (arg, expr) 
    else lookforHandlingCases xs label 

let (continueationCxt: ((spec list * string * (string * core_lang) * core_handler_ops) list) ref)  = ref [] 

let primitives = ["+"; "-"; "="]

let rec handling_spec env (spec:normalisedStagedSpec) (normal:(string * core_lang)) (ops:core_handler_ops) : spec list = 
  
  (*print_endline("\nhandling_spec =====> " ^ string_of_spec (normalisedStagedSpec2Spec spec));
*)
  let (normFormalArg, expRet) = normal in 
  let (effS, normalS) = spec in 
  match effS with 
  | [] -> 
    let (existiental, (p1, h1), (p2, h2), ret) = normalS in 

    let bindings = bindFormalNActual [normFormalArg] [ret] in 
    let current = [Exists existiental; Require(p1, h1); NormalReturn(p2, h2, ret)] in 
    let temp = infer_of_expression env [current] expRet in 
    instantiateSpecList bindings temp

    
  | x :: xs -> 
    let ret = match x.e_ret with 
    | Var ret -> ret
    | _ -> failwith "effect return is not var"

    in

    let (label, effactualArgs) = x.e_constr in
    (match lookforHandlingCases ops label with 
    | None -> concatenateEventWithSpecs (effectStage2Spec [x]) (handling_spec env (xs, normalS) normal ops )
    | Some (effFormalArg, exprEff) -> 
      (*print_string ("formal argument for label is " ^ effFormalArg ^ "\n"); *)
      let bindings = 
        match effFormalArg, effactualArgs with 
        | _, [] | None, _ -> [] 
        | Some e, effactualArg ::_ -> [(e, effactualArg)]
      in 
    let (p1, h1) = x.e_pre in
    let (p2, h2) = x.e_post in
      let current = [Exists x.e_evars; Require(p1, h1); 
        NormalReturn(p2, h2, UNIT)] in  (* Var ret *)

      let continueation_spec = normalisedStagedSpec2Spec (xs, normalS) in 
      let () = continueationCxt := ([continueation_spec],  ret, normal, ops) :: !continueationCxt in 
      let temp = infer_of_expression env [current] exprEff in 
      let () = continueationCxt := List.tl (!continueationCxt) in 

      instantiateSpecList bindings temp

    )


 
and infer_of_expression (env:meth_def list) (current:disj_spec) (expr:core_lang): disj_spec = 
  (*print_string (string_of_coreLang_kind expr ^ "\n"); *)
  match expr with
  | CValue v -> 
    let event = NormalReturn (True, EmptyHeap, v) in 
    concatenateSpecsWithEvent current [event]

  | CLet (str, expr1, expr2) -> 
    let phi1 = infer_of_expression env current expr1 in 
    List.flatten (List.map (fun spec -> 
      (*print_endline (string_of_spec(spec)); *)
      let retN = retrieve_return_value spec in 
      match retN with 
      | UNIT -> infer_of_expression env [spec] expr2
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
      | _ -> 
        if String.compare str "_" == 0 
        then infer_of_expression env [spec] expr2
        else 
          let bindings = bindFormalNActual [str] [retN] in 
          let phi2 = infer_of_expression env [spec] expr2 in 
          instantiateSpecList bindings phi2
    ) phi1)


  | CRef v -> 
    let freshVar = verifier_getAfreeVar () in 
    let event = NormalReturn (True, PointsTo(freshVar, v), Var freshVar) in 
    concatenateSpecsWithEvent current [Exists [freshVar];event]


  | CRead str -> 
    let freshVar = verifier_getAfreeVar ~from:str () in 
    let event = [Exists [freshVar];Require(True, PointsTo(str, Var freshVar)); 
      NormalReturn (True, PointsTo(str, Var freshVar) , Var freshVar)] in 
    concatenateSpecsWithEvent current event


  | CAssert (p, h) -> 
    let temp = concatenateSpecsWithEvent current [Require(p, h)] in 
    concatenateSpecsWithEvent temp [(NormalReturn(p, h, UNIT))]

  | CPerform (label, arg) -> 
        
    let arg = 
      match arg with 
      | Some v -> [v]
      | _ -> []
    in 
    let freshVar = verifier_getAfreeVar ~from:"res" () in 
    (* after adding the perfome stage, we need to add a normal return. *)
    concatenateSpecsWithEvent current 
    [Exists [freshVar];RaisingEff(True, EmptyHeap, (label,arg), Var freshVar);
    NormalReturn (True, EmptyHeap, Var freshVar)]


  | CResume v ->  
      (match !continueationCxt with 
      | [] -> failwith "resume in a wrong context"
      | (continue_specs, ret, normal, ops) :: _ -> 

          (*
          print_endline ("C = " ^ string_of_spec continue_spec);
          *)
          let bindings = bindFormalNActual [ret] [v] in 
          (* instantiate the rest of the stages *)

          (*print_endline (string_of_spec_list continue_specs); *)
          let continue_specs = renamingexistientalVar continue_specs in 
          (*print_endline ("=====\n" ^string_of_spec_list continue_specs);*)
    
          let instantiatedSpecs =  instantiateSpecList bindings continue_specs in 
          (* instantiate the pre stages *)
          let instantiatedCurrent =  instantiateSpecList bindings current in 
          (* after instantiate the pre stages, remove the existential quantifier for ret *)
          let instantiatedCurrent' = removeExist instantiatedCurrent ret in 

          let temp = 
            List.flatten (
              List.map  (fun a -> handling_spec env (normalise_spec a)  normal ops) instantiatedSpecs
            )
             in 
          concatenateSpecsWithSpec instantiatedCurrent' temp
      )

  | CFunCall (fname, actualArgs) -> 
    if List.mem fname primitives then begin
      match fname, actualArgs with
      | "+", [x1; x2] ->
        let event = NormalReturn (True, EmptyHeap, Plus(x1, x2)) in 
        concatenateSpecsWithEvent current [event]
      | "-", [x1; x2] ->
        let event = NormalReturn (True, EmptyHeap, Minus(x1, x2)) in 
        concatenateSpecsWithEvent current [event]
      | "=", [x1; x2] ->
        (* TODO bool values, or at least Eq constructor in term *)
        let event = NormalReturn (Atomic (EQ, x1, x2), EmptyHeap, UNIT) in 
        concatenateSpecsWithEvent current [event]
      | _ -> failwith (Format.asprintf "unknown primitive: %s, args: %s" fname (string_of_list string_of_term actualArgs))

    end else 
    let spec_of_fname =
      match retrieveSpecFromEnv fname env with 
      | None ->
        let ret = verifier_getAfreeVar () in
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
            | Var a -> (p, retrieveSpecFromEnv a env)
            | _ -> (p, None) (* if a is a lambda, get its spec here *)
            ) formalArgs actualArgs
          in
          instantiate_higher_order_functions fnArgs spec
        in
        (* Format.printf "after ho fns: %s@." (string_of_disj_spec spec); *)
        let bindings = bindFormalNActual (formalArgs) (actualArgs) in 
        let instantiatedSpec = instantiateSpecList bindings spec in 
        instantiatedSpec
        (*print_endline ("====\n"^ string_of_spec_list spec_of_fname);*)
    in
    concatenateSpecsWithSpec current spec_of_fname  

(* 
ex i; Norm(i->0, i); ex f4; 
Eff(emp, [], f4); 
ex f5 f6; 
req i->f5; 
Norm(i->f5, f5+1); 
req i->f6; 
Norm(i->f5+1, ()); Norm(emp, f4)
*)

  | CWrite  (str, v) -> 
    let freshVar = verifier_getAfreeVar () in 
    let event = [Exists [freshVar];Require(True, PointsTo(str, Var freshVar)); 
                  NormalReturn (True, PointsTo(str, v), UNIT)] in 
    concatenateSpecsWithEvent current event


  | CIfELse (v, expr2, expr3) -> 
    (* TODO missing bool *)
    let eventThen = NormalReturn (Atomic(EQ, v, term_true), EmptyHeap, UNIT) in 
    let eventElse = NormalReturn (Not(Atomic(EQ, v, term_true)), EmptyHeap, UNIT) in 
    let currentThen = concatenateSpecsWithEvent current [eventThen] in 
    let currentElse = concatenateSpecsWithEvent current [eventElse] in 
    (infer_of_expression env currentThen expr2) @ 
    (infer_of_expression env currentElse expr3)


  | CMatch (expr1, (normFormalArg, expRet), ops) ->
    let phi1 = infer_of_expression env [freshNormalReturnSpec] expr1 in 
    let afterHanldering = List.flatten (
      List.map (fun spec -> 
        (*print_endline("\nCMatch =====> " ^ string_of_spec spec); *)
        let normalisedSpec= (normalise_spec spec) in 

        handling_spec env  normalisedSpec (normFormalArg, expRet) ops
      ) phi1
    ) in 
    concatenateSpecsWithSpec current afterHanldering

 (*



    
*)