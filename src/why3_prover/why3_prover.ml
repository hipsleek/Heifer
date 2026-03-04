open Util.Strings

module Heifer = struct
  module Util = Util
end

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
      |> Heifer.Util.Lists.string_of_list Fun.id
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

(* Best-effort attempt to render VCs in a form that can be appended to the end of heifer.why for debugging *)
let pretty_print_debug_vc (lines : string) : string =
  let lines =
    lines |> String.split_on_char '\n'
    |> List.drop_while (fun s ->
        not (String.ends_with ~suffix:"(* use heifer.Heifer *)" s))
  in
  (* let indent = String.index_from (List.hd lines) 0 '(' - 2 in *)
  let lines =
    lines |> List.tl
    (* |> List.map (fun s -> String.sub s indent (String.length s - indent)) *)
    |> List.filter (fun s ->
        let s = String.trim s in
        s <> "" && s <> "end")
  in
  Format.asprintf {|module M
  use Heifer
%s
end|} (lines |> String.concat "\n")

let log_vc show_goal tasks =
  if show_goal then
    let debug_vc =
      tasks
      |> List.map (fun t -> Format.asprintf "%a" Why3.Pretty.print_task t)
      |> List.map pretty_print_debug_vc
    in
    Format.printf "@[<v>%a@]@." (Fmt.list Fmt.string) debug_vc

(* Exposes the structure of tasks for debugging.
  A task is an option of a reversed linked list of tdecls.
  A tdecl is either a decl, a use, etc.
  decls are types, data, logic, etc. *)
let[@warning "-32"] rec inspect_task task =
  match task with
  | None -> ()
  | Some task_hd ->
      inspect_task task_hd.Task.task_prev;
      let decl = task_hd.Task.task_decl in
      (match decl.Theory.td_node with
      | Theory.Decl { Decl.d_node = d; _ } ->
          (match d with
          | Decl.Dtype _ -> Format.printf "Dtype@."
          | Decl.Ddata _ -> Format.printf "Ddata@."
          | Decl.Dparam l ->
              let ty =
                match l.ls_value with
                | None -> "no type"
                | Some t -> Format.asprintf "%a" Pretty.print_ty t
              in
              Format.printf "Dparam %a : %s@." Pretty.print_ls l ty
          | Decl.Dlogic _ -> Format.printf "Dlogic@."
          | Decl.Dind (kind, decl) ->
              (* inductive definition, not a term of inductive type *)
              let kind =
                match kind with
                | Coind -> "Coind"
                | Ind -> "Ind"
              in
              let decl =
                match decl with
                | (l, _) :: _ -> Format.asprintf "%a" Pretty.print_ls l
                | _ -> failwith "asd"
              in
              Format.printf "Dind %s %s@." kind decl
          | Decl.Dprop (kind, pr, f) ->
              (* hypotheses are in here too, typically as axioms *)
              let kind =
                match kind with
                | Decl.Plemma -> "Plemma"
                | Decl.Paxiom -> "Paxiom"
                | Decl.Pgoal -> "Pgoal"
              in
              Format.printf "Dprop %s %a: %a@." kind Pretty.print_pr pr
                (* pr.Decl.pr_name.Ident.id_string *)
                Why3.Pretty.print_term f)
      | Theory.Use { th_name; _ } ->
          Format.printf "Use (%s)@." th_name.id_string
      | Theory.Clone _ -> Format.printf "Clone@."
      | Theory.Meta _ -> Format.printf "Meta@.")

(* let ( let* ) m f = List.concat_map f m
let pure a = [a] *)

(* let rec fold_m f xs init =
  match xs with
  | [] -> pure init
  | x :: xs1 ->
      let* acc = fold_m f xs1 init in
      f x acc *)

let apply_transform_args name env args task =
  let naming_table = Why3.Args_wrapper.build_naming_tables task in
  Trans.apply_transform_args name env args naming_table "whyml" task

(** Superseded, but an example of a repeat-match loop using Why3's API *)
let _intro_and_invert_types _show_goal task =
  let open Heifer.Util.Lists.Monad in
  let rec aux task =
    (* log_vc show_goal [task]; *)
    try
      let goal_fmla = Task.task_goal_fmla task in
      match goal_fmla.t_node with
      | Tquant (Tforall, q) ->
          let xs, _, _body = Term.t_open_quant q in
          let xs = List.map (fun x -> x.Term.vs_name.id_string) xs in
          let xs =
            (* intro one name at a time. not sure why we can't just intro all at once... *)
            [List.hd xs]
          in
          let* task = apply_transform_args "intros" why3_env xs task in
          aux task
      | Tbinop (Timplies, p, _) ->
          (match p.t_node with
          | Term.Tapp (f, _) ->
              (match f.ls_name.id_string with
              | "is_int" ->
                  let* task =
                    Trans.apply_transform "inversion_pr" why3_env task
                  in
                  aux task
              | _ ->
                  let* task =
                    apply_transform_args "intros" why3_env ["H"] task
                  in
                  aux task)
          | _ -> [task])
      | _ -> [task]
    with Task.GoalNotFound -> [task]
  in
  aux task

(** We currently rely on the file ending with an inductive definition as the
    marker for what was introduced. Produces more recently introduced hypotheses
    first. *)
(* let get_introduced_hypotheses t =
  let decls = Task.task_decls t in
  decls |> List.rev
  |> List.take_while (fun d ->
      match d.Decl.d_node with
      | Decl.Dind _ -> false
      | _ -> true) *)

(*
let categorise_hypotheses t =
  let decls = get_introduced_hypotheses t in
  let compute, invert =
    List.fold_right
      (fun c (comp, inv) ->
        match c.Decl.d_node with
        | Decl.Dprop (Decl.Paxiom, pr, term) ->
            (match term.t_node with
            | Term.Tapp (l, _) ->
                (match l.ls_name.id_string with
                | "is_int" | "is_int_list" -> (comp, pr :: inv)
                | _ -> (pr :: comp, inv))
            | _ ->
                (* not an application, so doubtful as to whether we should compute in it *)
                (comp, inv))
        | _ ->
            (* not an axiom, so probably not something we introduced *)
            (comp, inv))
      decls ([], [])
  in
  (compute, invert)
*)

let attempt_proof show_goal task =
  (* inspect_task task; *)
  let open Heifer.Util.Lists.Monad in
  let tasks =
    (* simplification is necessary, regardless of whether we use any other tactics,
      as it e.g. removes redundant quantified args, which we don't check for when translating *)
    let* task = Trans.apply_transform "simplify_formula" why3_env task in

    (* the strategy is: introduce everything, invert the type hypotheses, then simplify in the premises *)
    let* task = Trans.apply_transform "introduce_premises" why3_env task in

    (* let comp, inv = categorise_hypotheses task in *)

    (* invert all the type premises once, then introduce and subst *)
    (* let* task =
      fold_m
        (fun c t ->
          let name = c.Decl.pr_name.Ident.id_string in
          apply_transform_args "inversion_arg_pr" why3_env [name] t)
        inv task
    in *)
    let* task = Trans.apply_transform "introduce_premises" why3_env task in
    (* this crashes *)
    (* let* task = Trans.apply_transform "subst_all" why3_env task in *)
    let* task = apply_transform_args "subst_all" why3_env [] task in

    (* compute in hypotheses *)
    (* this cause a problem at the moment *)
    (* let* task =
      let axioms = comp in
      (* print the task *)
      fold_m
        (fun c t ->
          let use_string_interface = true in
          match use_string_interface with
          | false ->
              Trans.apply (Compute.normalize_hyp None (Some c) why3_env) t
          | true ->
              let name = c.Decl.pr_name.Ident.id_string in
              Format.printf "arg_name: %s\n" name;
              apply_transform_args "compute_hyp" why3_env ["in"; name] t)
        axioms task
    in *)

    (* computing in the goal seems unnecessary and sometimes causes more blowup *)
    (* let* task = Trans.apply_transform "compute_in_goal" why3_env task in *)
    pure task
  in

  log_vc show_goal tasks;

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
    ["CVC4"; "Z3"; "Alt-Ergo"]
    (* ["CVC4"; "Z3"] *)
    |> List.filter_map (fun prover ->
        try
          ensure_prover_loaded prover;
          Some (get_prover_config prover)
        with _ -> None)
  in

  if List.is_empty provers then
    failwith "why3 prover: No provers found; check your configuration";

  (* try each task, on all possible provers *)
  let attempt_task (pconf, pdriver) task =
    let result1 =
      Call_provers.wait_on_call
        (Driver.prove_task
           ~limits:
             { Call_provers.empty_limits with Call_provers.limit_time = 0.5 }
           ~config:why3_config_main ~command:pconf.Whyconf.command pdriver task)
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
        failwith (explain (Format.sprintf "reported error: %s" s))
  in
  let combine_prover_results (name1, r1) (name2, r2) =
    match ((name1, r1), (name2, r2)) with
    | (_, `Valid), (_, `Unknown _) | (_, `Valid), (_, `Valid) -> (name1, `Valid)
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

let really_prove show_goal goal =
  let open Ptree in
  let open Ptree_helpers in
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
  if show_goal then
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
  let start_time = Why3_prover_statistics.current_time () in
  let result = mods
    |> Wstdlib.Mstr.map (fun m ->
        let tasks = Task.split_theory m.Pmodule.mod_theory None None in
        combine_task_results "Goal" (List.map (attempt_proof show_goal) tasks))
    |> Wstdlib.Mstr.bindings
    |> List.map (fun (_, result) -> result)
    |> combine_task_results "Module"
  in
  let end_time = Why3_prover_statistics.current_time () in
  Why3_prover_statistics.add_smt_time (end_time -. start_time);
  result

let prove ?(show_goal = false) goal =
  (* try *)
  really_prove show_goal goal
(* with
  | Failure s -> `Failure s
  | e -> `Failure (Printexc.to_string e) *)

let is_translatable = Translate.is_translatable
let reset_statistics = Why3_prover_statistics.reset_statistics
let get_smt_time = Why3_prover_statistics.get_smt_time
