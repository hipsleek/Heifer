open Util
open Why3

let why3_config = Whyconf.init_config None
let why3_config_main = Whyconf.get_main why3_config

let why3_env : Env.env =
  (* let extra_paths : SSet.t =
    let rec find_dune_project dir =
      if Sys.file_exists (dir ^ "/dune-project") then Some dir
      else if dir = "/" then None
      else find_dune_project (Filename.dirname dir)
    in
    let cwd = Sys.getcwd () in
    SSet.of_list (List.concat
      [
        [cwd];
        Option.to_list (find_dune_project cwd);
        (try [Filename.dirname Sys.argv.(1)] with _ -> []);
      ])
  in *)
  let cwd = Sys.getcwd () in
  (* Format.printf "cwd %s@." cwd; *)
  let load_path =
    (* SSet.of_list *)
    cwd :: Whyconf.loadpath why3_config_main
    (* |> SSet.union extra_paths *)
    (* |> SSet.to_list *)
  in
  (* Debug.debug ~at:4 ~title:"why load path" "%s"
    (string_of_list Fun.id load_path); *)
  Env.create_env load_path

let combine_task_results label task_results =
  (* let open Provers_common in *)
  if
    List.for_all
      (function
        | `Valid -> true
        | _ -> false)
      task_results
  then `Valid
  else if
    List.exists
      (function
        | `Invalid -> true
        | _ -> false)
      task_results
  then `Invalid
  else
    let explanation =
      task_results
      |> List.mapi (fun i result -> (i, result))
      |> List.filter_map (function
        | i, `Unknown s -> Some (Format.sprintf "%s %d: %s" label i s)
        | _ -> None)
      |> String.concat "\n"
    in
    `Unknown explanation

let prover_configs : (Whyconf.config_prover * Why3.Driver.driver) SMap.t ref =
  ref SMap.empty

let string_of_prover p =
  Format.asprintf "%s %s%s" p.Whyconf.prover_name p.prover_version
    (match p.prover_altern with
    | "" -> ""
    | a -> "/" ^ a)

let string_of_prover_result = function
  | `Valid -> "valid"
  | `Invalid -> "invalid"
  | `Unknown s -> "unknown (" ^ s ^ ")"

let load_prover_config name : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover name in
  let provers = Whyconf.filter_provers why3_config fp in
  if Whyconf.Mprover.is_empty provers then begin
    failwith
      (Format.asprintf "Prover %s not installed or not configured@." name)
  end
  else begin
    let _alts =
      Whyconf.(
        Mprover.map (fun cp -> string_of_prover cp.prover) provers
        |> Mprover.bindings |> List.map snd)
      |> string_of_list Fun.id
    in
    let _p, conf = Whyconf.Mprover.min_binding provers in
    (* Debug.debug ~at:2 ~title:"loaded prover" "defaulting to %s out of:\n%s"
      (string_of_prover p) alts; *)
    conf
  end

let load_prover_driver conf name =
  try Driver.load_driver_for_prover why3_config_main why3_env conf
  with e ->
    Format.printf "Failed to load driver for %s: %a@." name
      Exn_printer.exn_printer e;
    raise e

let ensure_prover_loaded name =
  match SMap.find_opt name !prover_configs with
  | None ->
      let conf = load_prover_config name in
      prover_configs :=
        SMap.add name (conf, load_prover_driver conf name) !prover_configs
  | Some _ -> ()

let get_prover_config name = SMap.find name !prover_configs

let attempt_proof task1 =
  (* Format.printf "task: %a@." Why3.Pretty.print_task task1; *)
  let tasks = Trans.apply_transform "simplify_formula" why3_env task1 in

  (* Debug.debug ~at:5 ~title:"WhyML VC" "%a"
    (Format.pp_print_list Why3.Pretty.print_task)
    tasks; *)

  (* only do this once, not recursively *)
  (* let tasks =
    tasks
    |> List.concat_map (fun t ->
           (* let@ _ = silence_stderr in *)
           (* Trans.apply_transform "induction_ty_lex" why3_env t *)
           [t])
    (* |> List.concat_map (Trans.apply_transform "split_goal" why3_env) *)
  in *)

  (* it's unlikely the provers will change location in the span of one task *)
  let provers =
    (* ["Alt-Ergo"; "CVC4"; "Z3"] *)
    (* ["Alt-Ergo"] *)
    (* ["Z3"] *)
    ["CVC4"; "Z3"]
    |> List.filter_map (fun prover ->
        try
          ensure_prover_loaded prover;
          Some (get_prover_config prover)
        with _ -> None)
  in
  if List.is_empty provers then
    failwith
      (* raise *)
      (* Provers_common.Prover_error *)
      "why3 prover: No provers found; check your configuration"
  else
    (* try each task, on all possible provers *)
    let attempt_task (pconf, pdriver) task =
      (* : Provers_common.prover_result = *)
      let result1 =
        Call_provers.wait_on_call
          (Driver.prove_task
             ~limits:
               { Call_provers.empty_limits with Call_provers.limit_time = 0.5 }
             ~config:why3_config_main ~command:pconf.Whyconf.command pdriver
             task)
      in
      let explain ctx =
        Format.sprintf "Prover %s: %s" pconf.prover.prover_name ctx
      in
      match result1.pr_answer with
      | Valid -> `Valid
      | Invalid -> `Invalid
      | Timeout -> `Unknown (explain "timeout")
      | Unknown s -> `Unknown (explain (Format.sprintf "unknown: %s" s))
      | OutOfMemory -> `Unknown (explain "out of memory")
      | StepLimitExceeded -> `Unknown (explain "step limit exceeded")
      | Failure s | HighFailure s ->
          failwith
            (* raise *)
            ((* Provers_common.Prover_error *)
             explain
               (Format.sprintf "reported error: %s" s))
    in
    let combine_prover_results (name1, r1) (name2, r2) =
      (* let open Provers_common in *)
      match ((name1, r1), (name2, r2)) with
      | (_, `Valid), (_, `Unknown _) | (_, `Valid), (_, `Valid) ->
          (name1, `Valid)
      | (_, `Unknown _), (_, `Valid) -> (name2, `Valid)
      | (_, `Invalid), (_, `Unknown _) | (_, `Invalid), (_, `Invalid) ->
          (name1, `Invalid)
      | (_, `Unknown _), (_, `Invalid) -> (name2, `Invalid)
      | (p1, (`Valid as r1)), (p2, (`Invalid as r2))
      | (p2, (`Invalid as r2)), (p1, (`Valid as r1)) ->
          let explanation =
            Format.sprintf "Provers %s (%s) and %s (%s) disagree on result" p1
              (string_of_prover_result r1)
              p2
              (string_of_prover_result r2)
          in
          (* raise (Provers_common.Prover_error explanation) *)
          failwith explanation
      | (_, `Unknown s1), (_, `Unknown s2) -> (name1, `Unknown (s1 ^ "\n" ^ s2))
    in
    let attempt_task_on_provers provers task =
      let open Whyconf in
      let prover_results =
        List.map
          (fun ((pconf, _) as prover) ->
            (pconf.prover.prover_name, attempt_task prover task))
          provers
      in
      List.fold_left combine_prover_results
        ("dummy", `Unknown "[no prover results found]")
        prover_results
    in
    let task_results =
      tasks
      |> List.map (attempt_task_on_provers provers)
      |> List.map (fun (_, result) -> result)
    in
    combine_task_results "Task" task_results

(* let prelude = {|
module Heifer
 goal G2: true
 let a = 1
end
  |} *)

let really_prove goal =
  let open Ptree in
  let open Ptree_helpers in
  (* let ass, goal = f () in *)
  let vc_mod =
    (* whether to generate

       goal g : forall x*. ass => ex x*. goal

       or

       constants x*
       axiom ass
       goal g : ex x*. goal
    *)
    let monolithic_goal = true in

    (* start building goal *)
    (* let universally_quantified =
      []
      (* SMap.merge_arbitrary
        (collect_variables#visit_pi () ass)
        (collect_variables#visit_pi () goal)
      |> SMap.to_list *)
    in *)
    let statement =
      (* let assumptions = Translate.prop_to_whyml ass in *)
      let goal1 =
        let binders = [] in
        (* vars_to_params qtf in *)
        match binders with
        | [] -> Translate.term_to_whyml goal
        | _ :: _ ->
            term
              (Tquant (Dterm.DTexists, binders, [], Translate.term_to_whyml goal))
      in
      match monolithic_goal with
      | false ->
          [
            (* Dprop (Decl.Paxiom, ident "ass1", Translate.prop_to_whyml ass); *)
            Dprop (Decl.Pgoal, ident "goal1", goal1);
          ]
      | true ->
          (* let forall_binders =
          []
          (* vars_to_params universally_quantified *)
        in *)
          (* let impl = term (Tbinop (assumptions, Dterm.DTimplies, goal1)) in
        let goal2 =
          match forall_binders with
          | [] -> impl
          | _ :: _ -> term (Tquant (Dterm.DTforall, forall_binders, [], impl))
        in *)
          [Dprop (Decl.Pgoal, ident "goal1", goal1)]
    in

    let fns =
      []
      (* match
        (* Globals.pure_fns () *)
        []
        (* |> List.map (fun (name, fn) -> (name, Hipcore.Typedhip.Untypehip.untype_pure_fn_def fn)) *)
      with
      | [] -> []
      | f ->
        let ff =
          List.map
            (fun (k, fn) ->
              {
                ld_loc = Loc.dummy_position;
                ld_ident = ident k;
                ld_params =
                  List.map
                    (fun (p, t) ->
                      ( Loc.dummy_position,
                        Some (ident p),
                        false,
                        type_to_whyml t ))
                    fn.pf_params;
                ld_type = Some (type_to_whyml fn.pf_ret_type);
                ld_def = Some (core_lang_to_whyml fn.pf_body);
              })
            f
        in
        [Dlogic ff] *)
    in

    let parameters =
      []
      (* match monolithic_goal with
      | true -> []
      | false ->
        [
          Dlogic
            (universally_quantified
            |> List.map (fun v ->
                let type_of_parameter = type_of_binder v in
                {
                  ld_loc = Loc.dummy_position;
                  ld_ident = ident (ident_of_binder v);
                  ld_params = [];
                  ld_type = Some (type_to_whyml type_of_parameter);
                  ld_def = None;
                }));
        ] *)
    in

    let imports =
      let extra =
        (* Globals.global_environment.pure_fn_types |> SMap.bindings
        |> List.map (fun (_, p) -> p.pft_logic_path)
        |> List.sort_uniq compare
        |> List.map (use ~import:false) *)
        []
      in
      [
        (* use ~import:false ["int"; "Int"]; *)
        (* use ~import:false ["bool"; "Bool"]; *)
        (* use ~import:false ["list"; "List"]; *)
        use ~import:false ["heifer"; "Heifer"];
      ]
      @ extra
    in
    (ident "M", List.concat [imports; fns; parameters; statement])
  in

  (* let prelude = Lexer.parse_mlw_file (Lexing.from_string prelude) in *)
  let mlw_file = Modules [vc_mod] in
  (* Debug.debug ~at:4 ~title:"mlw file" "%a" *)
  Format.printf "%a@." (Mlw_printer.pp_mlw_file ~attr:true) mlw_file;
  let mods =
    try Typing.type_mlw_file why3_env [] "myfile.mlw" mlw_file
    with Loc.Located (loc, e) ->
      (* A located exception [e] *)
      (* if Debug.in_debug_mode () then ( *)
      (* Debug.debug ~at:4 ~title:"failed due to type error" ""; *)
      let msg = Format.asprintf "%a" Exn_printer.exn_printer e in
      (* let msg = Printexc.to_string e in *)
      (* Format.printf "%a@."
        (Mlw_printer.with_marker ~msg loc (Mlw_printer.pp_mlw_file ~attr:true))
        mlw_file; *)
      let msg =
        Format.asprintf "failed to construct module: %s, %a@." msg
          Loc.pp_position loc
      in
      (* ); *)
      (* Format.printf "%s@." msg *)
      failwith msg
  in
  (* there will be only one module *)
  mods
  |> Wstdlib.Mstr.map (fun m ->
      let tasks = Task.split_theory m.Pmodule.mod_theory None None in
      combine_task_results "Goal" (List.map attempt_proof tasks))
  |> Wstdlib.Mstr.bindings
  |> List.map (fun (_, result) -> result)
  |> combine_task_results "Module"

let prove goal =
  (* try *)
  really_prove goal
(* with
  | Failure s -> `Failure s
  | e -> `Failure (Printexc.to_string e) *)

let is_translatable = Translate.is_translatable
