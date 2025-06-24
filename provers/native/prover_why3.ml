module Hipdebug = Debug
open Why3
module Debug = Hipdebug

(* open this second, so it gets precedence for shadowed modules *)
open Hipcore
open Hiptypes
open Types

let prover_configs : (Whyconf.config_prover * Why3.Driver.driver) SMap.t ref =
  ref SMap.empty

(* top-level side effects *)
let why3_config = Whyconf.init_config None
let why3_config_main = Whyconf.get_main why3_config

let () =
  if not (Debug.in_debug_mode ()) then
    Loc.set_warning_hook (fun ?loc:_ _msg -> ())

let why3_env : Env.env =
  let extra_paths : SSet.t =
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
  in
  let load_path = SSet.of_list (Whyconf.loadpath why3_config_main)
    |> SSet.union extra_paths
    |> SSet.to_list
  in
  Debug.debug ~at:4 ~title:"why load path" "%s"
    (string_of_list Fun.id load_path);
  Env.create_env load_path

let string_of_prover p =
  Format.asprintf "%s %s%s" p.Whyconf.prover_name p.prover_version
    (match p.prover_altern with "" -> "" | a -> "/" ^ a)

let load_prover_config name : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover name in
  let provers = Whyconf.filter_provers why3_config fp in
  if Whyconf.Mprover.is_empty provers then begin
    failwith
      (Format.asprintf "Prover %s not installed or not configured@." name)
  end
  else begin
    let alts =
      Whyconf.(
        Mprover.map (fun cp -> string_of_prover cp.prover) provers
        |> Mprover.bindings
        |> List.map snd)
      |> string_of_list Fun.id
    in
    let p, conf = Whyconf.Mprover.min_binding provers in
    Debug.debug ~at:2 ~title:"loaded prover" "defaulting to %s out of:\n%s"
      (string_of_prover p) alts;
    conf
  end

let load_prover_driver conf name =
  try Driver.load_driver_for_prover why3_config_main why3_env conf
  with e ->
    Format.printf
      "Failed to load driver for %s: %a@."
      name Exn_printer.exn_printer e;
    raise e

let ensure_prover_loaded name =
  match SMap.find_opt name !prover_configs with
  | None ->
    let conf = load_prover_config name in
    prover_configs :=
      SMap.add name (conf, load_prover_driver conf name) !prover_configs
  | Some _ -> ()

let get_prover_config name = SMap.find name !prover_configs

let silence_stderr
    (* : (unit -> 'a) -> 'a = *)
    (* let null = open_out "/dev/null" in *)
    (* fun f -> *)
      f =
  let null = open_out "/dev/null" in
  Format.pp_set_formatter_out_channel Format.err_formatter null;
  let result = f () in
  Format.pp_set_formatter_out_channel Format.err_formatter stderr;
  close_out null;
  result

let attempt_proof task1 =
  (* Format.printf "task: %a@." Why3.Pretty.print_task task1; *)
  let tasks = Trans.apply_transform "simplify_formula" why3_env task1 in

  Debug.debug ~at:5 ~title:"WhyML VC" "%a"
    (Format.pp_print_list Why3.Pretty.print_task)
    tasks;

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
  (* try each task, on all possible provers *)
  List.for_all
    (fun task ->
      List.exists
        (fun (pconf, pdriver) ->
          let result1 =
            Call_provers.wait_on_call
              (Driver.prove_task
                 ~limits:
                   {
                     Call_provers.empty_limits with
                     Call_provers.limit_time = 0.5;
                   }
                 ~config:why3_config_main ~command:pconf.Whyconf.command pdriver
                 task)
          in
          (* Format.printf "%s: %a@." prover
             (Call_provers.print_prover_result ?json:None)
             result1; *)
          match result1.pr_answer with Valid -> true | _ -> false)
        provers)
    tasks

(* old approach which uses the low-level why3 (not whyml) API.

   - requires all types to be provided, which is a problem for pure functions

   - also requires a stateful, lazy/interleaved approach to figuring out what
   theories to load while translating the pure formula, which can't be easily
   stratified - we need the formula to analyze it for theories, and we need the
   theories in order to translate other parts of the formula

   the main reason i can think of to use this is performance (to avoid running
   the whyml type checker and inferring types over and over again), but that
   would us to type our source language.
*)
module LowLevel = struct
  (** theory identifier *)
  module Tid = struct
    type t = string list * string

    let compare = compare
  end

  let string_of_tid = string_of_pair (string_of_list Fun.id) Fun.id

  module TMap = Map.Make (Tid)

  (** Mutable data structure for keeping track of which theories have been loaded *)
  module Theories = struct
    type t = Theory.theory TMap.t ref

    let create () = ref TMap.empty
    let fold f t init = List.fold_right f (TMap.bindings !t) init

    (* Some common ones we use *)
    let string = (["string"], "String")
    let int = (["int"], "Int")
    let bool = (["bool"], "Bool")
    let list = (["list"], "List")
    let extras = (["extras"], "Extras")

    let needed tid t =
      (* Format.printf "needed: %s@." (string_of_tid tid); *)
      match TMap.find_opt tid !t with
      | None ->
        (* Format.printf "read: %s@." (string_of_tid tid); *)
        let path, name = tid in
        t := TMap.add tid (Env.read_theory why3_env path name) !t
      | Some _ -> ()

    let get_symbol th sym t =
      needed th t;
      match TMap.find_opt th !t with
      | None ->
        failwith (Format.asprintf "theory with symbol %s not loaded" sym)
      | Some t ->
        (* Format.printf "--- get symbol@.";
           Wstdlib.Mstr.bindings t.Theory.th_export.ns_ls
           |> List.iter (fun (k, v) ->
                  Format.printf "%s %a@." k Why3.Pretty.print_ls v);
           Format.printf "---@."; *)
        Theory.ns_find_ls t.Theory.th_export [sym]

    let get_type_symbol th sym t =
      needed th t;
      match TMap.find_opt th !t with
      | None ->
        failwith (Format.asprintf "theory with type symbol %s not loaded" sym)
      | Some t -> Theory.ns_find_ts t.Theory.th_export [sym]
  end

  module TSet = Set.Make (Tid)

  type env = {
    mutable forall : Term.vsymbol SMap.t;
    mutable fn_names : Term.lsymbol SMap.t;
    theories : Theories.t;
        (* TODO consider making this global for performance *)
    tenv : typ SMap.t;
    exists : Term.vsymbol SMap.t;
    letbound : Term.vsymbol SMap.t;
  }

  let rec type_to_why3 env (t : typ) =
    match t with
    | Unit -> Ty.ty_tuple []
    | List_int ->
      Theories.(needed int env.theories);
      Ty.ty_app Theories.(get_type_symbol list "list" env.theories) [Ty.ty_int]
    | TyString ->
      Theories.(needed string env.theories);
      Ty.ty_str
    | Int ->
      Theories.(needed int env.theories);
      Ty.ty_int
    | Bool ->
      Theories.(needed bool env.theories);
      Ty.ty_bool
    | Lamb -> Ty.ty_int
    | TVar _ ->
      (* failwith "unknown type" *)
      (* default to int *)
      Theories.(needed int env.theories);
      Ty.ty_int
    | Arrow (t1, t2) -> Ty.ty_func (type_to_why3 env t1) (type_to_why3 env t2)
    | TConstr _ -> failwith "general ADTs not implemented"

  let rec term_to_why3 env (t : term) =
    (* Format.printf "term %s@." (Pretty.string_of_term t); *)
    match t with
    | Const ValUnit -> (Term.t_tuple [], Unit)
    | Const (Num i) ->
      Theories.(needed int env.theories);
      (Term.t_nat_const i, Int)
    | TLambda (_, _, _, _) ->
      Theories.(needed int env.theories);
      failwith "not updated" (* (Term.t_nat_const (Subst.hash_lambda t), Int) *)
    | Var v when SMap.mem v env.tenv ->
      let ty1 = SMap.find v env.tenv (* |> Option.value ~default:Int *) in
      let ty = type_to_why3 env ty1 in
      let name =
        match SMap.find_opt v env.exists with
        | Some v -> Term.t_var v
        | None ->
          (match SMap.find_opt v env.forall with
          | None ->
            let name = Ident.id_fresh v in
            (* let sym = Term.create_lsymbol name [] (Some ty) in *)
            let sym = Term.create_vsymbol name ty in
            env.forall <- SMap.add v sym env.forall;
            Term.t_var sym
            (* Term.t_app sym [] (Some ty) *)
          | Some vv ->
            (* Term.t_app vv [] (Some ty) *)
            Term.t_var vv)
      in
      (* Format.printf "var %s : %s@." v
         Pretty.(
           string_of_option string_of_type (SMap.find_opt v env.tenv)); *)
      (name, ty1)
    | Var v -> failwith (Format.asprintf "variable %s has no type" v)
    | BinOp (SConcat, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol string "concat" env.theories)
          [a1; b1],
        Int )
    | BinOp (Plus, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix +" env.theories)
          [a1; b1],
        Int )
    | BinOp (Minus, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix -" env.theories)
          [a1; b1],
        Int )
    | Rel (EQ, a, b) ->
      let a1, t1 = term_to_why3 env a in
      let b1, t2 = term_to_why3 env b in
      ( (match (t1, t2) with
        | Int, Int ->
          Term.fs_app
            (* Theories.(get_symbol int "infix =" env.theories) *)
            Theories.(get_symbol extras "eqi" env.theories)
            [a1; b1] Ty.ty_bool
        | Bool, Bool ->
          Term.t_app_infer
            Theories.(get_symbol extras "eqb" env.theories)
            [a1; b1]
        | _, _ ->
          failwith
            (Format.asprintf "equality not defined between types %s and %s"
               (Pretty.string_of_type t1) (Pretty.string_of_type t2))),
        Bool )
    | Rel (GT, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix >" env.theories)
          [a1; b1],
        Bool )
    | Rel (LT, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix <" env.theories)
          [a1; b1],
        Bool )
    | Rel (GTEQ, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix >=" env.theories)
          [a1; b1],
        Bool )
    | Rel (LTEQ, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer
          Theories.(get_symbol int "infix <=" env.theories)
          [a1; b1],
        Bool )
    | Const TTrue ->
      Theories.(needed bool env.theories);
      (Term.t_bool_true, Bool)
    | Const TFalse ->
      Theories.(needed bool env.theories);
      (Term.t_bool_false, Bool)
    | BinOp (TAnd, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer Theories.(get_symbol bool "andb" env.theories) [a1; b1],
        Bool )
      (* Term.fs_app  [] Ty.ty_bool *)
      (* Term.t_and (term_to_why3 env a) (term_to_why3 env b) *)
    | BinOp (TOr, a, b) ->
      (* Term.t_and (term_to_why3 env a) (term_to_why3 env b) *)
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      ( Term.t_app_infer Theories.(get_symbol bool "orb" env.theories) [a1; b1],
        Bool )
    | TNot a ->
      (* Term.t_not (term_to_why3 env a) *)
      let a1, _ = term_to_why3 env a in
      ( Term.t_app_infer Theories.(get_symbol bool "notb" env.theories) [a1],
        Bool )
    | BinOp (TCons, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      (* let open Pretty in *)
      (* Format.printf "cons %s %s @." (string_of_term a) (string_of_term b); *)
      ( Term.t_app
          Theories.(get_symbol list "Cons" env.theories)
          [a1; b1]
          (Some (type_to_why3 env List_int)),
        List_int )
      (* inferring types leads to issues reconciling types between systems *)
      (* Term.t_app_infer
         (get_theory_symbol env.list_theory "Cons")
         [term_to_why3 env a; term_to_why3 env b] *)
    | Const Nil ->
      (* Term.t_app_infer (get_theory_symbol env.list_theory "Nil") [] *)
      ( Term.t_app
          Theories.(get_symbol list "Nil" env.theories)
          []
          (Some (type_to_why3 env List_int)),
        List_int )
    | TApp (s, args) when Globals.is_pure_fn_defined s ->
      let args1 = List.map (term_to_why3 env) args |> List.map fst in
      let defn = Globals.pure_fn s
      (* |> Hipcore.Typedhip.Untypehip.untype_pure_fn_def *)
      in
      let ret_typ = type_to_why3 env defn.pf_ret_type in
      (* Format.printf "app %s@." s; *)
      ( Term.t_app (SMap.find s env.fn_names) args1 (Some ret_typ),
        defn.pf_ret_type )
    | TApp (s, _) -> failwith (Format.asprintf "unknown function term %s" s)
    | BinOp (TPower, _, _) -> failwith "TPower nyi"
    | BinOp (TTimes, _, _) -> failwith "TTimes nyi"
    | BinOp (TDiv, _, _) -> failwith "TDiv nyi"
    | TTuple _ -> failwith "TTupple nyi"
    | Const (TStr _) -> failwith "TStr nyi"

  let rec pi_to_why3 env (pi : pi) =
    (* Format.printf "pi %s@." (Pretty.string_of_pi pi); *)
    match pi with
    | True -> Term.t_true
    | False -> Term.t_false
    | Atomic (EQ, a, b) ->
      let a1, t1 = term_to_why3 env a in
      let b1, t2 = term_to_why3 env b in
      (match (t1, t2) with
      | Bool, Bool ->
        (* Term.t_app_infer Theories.(get_symbol extras "eqb" env.theories) [a1; b1] *)
        Term.t_equ a1 b1
      | _, _ ->
        (* this seems to be ok *)
        Term.t_equ a1 b1)
    | Atomic (GT, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      Term.t_app_infer Theories.(get_symbol int "infix >" env.theories) [a1; b1]
    | Atomic (LT, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      Term.t_app_infer Theories.(get_symbol int "infix <" env.theories) [a1; b1]
    | Atomic (GTEQ, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      Term.t_app_infer
        Theories.(get_symbol int "infix >=" env.theories)
        [a1; b1]
    | Atomic (LTEQ, a, b) ->
      let a1, _ = term_to_why3 env a in
      let b1, _ = term_to_why3 env b in
      Term.t_app_infer
        Theories.(get_symbol int "infix <=" env.theories)
        [a1; b1]
    | And (a, b) -> Term.t_and (pi_to_why3 env a) (pi_to_why3 env b)
    | Or (a, b) -> Term.t_or (pi_to_why3 env a) (pi_to_why3 env b)
    | Imply (a, b) -> Term.t_implies (pi_to_why3 env a) (pi_to_why3 env b)
    | Not a -> Term.t_not (pi_to_why3 env a)
    | Predicate (_, _) -> failwith "nyi Predicate"
    | Subsumption (_, _) -> pi_to_why3 env True

  let rec expr_to_why3 env e =
    (* Format.printf "expr %s@." (Pretty.string_of_core_lang e); *)
    match e with
    | CLet (v, e1, a) ->
      (* Format.printf "??%s@." (Pretty.string_of_core_lang e); *)
      let h = Term.create_vsymbol (Ident.id_fresh v) (type_to_why3 env Int) in
      let e2 = expr_to_why3 env e1 in
      let a1 =
        expr_to_why3 { env with letbound = SMap.add v h env.letbound } a
      in
      (* a1 *)
      Term.t_let e2 (Term.t_close_bound h a1)
      (* failwith "sdasd" *)
    | CSequence (_e1, _e2) ->
        failwith "CSequence"
    | CValue t ->
      let t, _ty = term_to_why3 env t in
      t
    | CIfELse (_, _, _) -> failwith "unimplemented CIfELse"
    | CFunCall (s, args) when Globals.is_pure_fn_defined s ->
      (* SMap.mem s env.names *)
      let args1 = List.map (term_to_why3 env) args |> List.map fst in
      let fn = Globals.pure_fn s
      (* |> Hipcore.Typedhip.Untypehip.untype_pure_fn_def *)
      in
      (* Format.printf "%s@." s; *)
      Term.t_app (SMap.find s env.fn_names) args1
        (Some (type_to_why3 env fn.pf_ret_type))
      (* failwith "unimplemented CFunCall" *)
    | CFunCall (s, _) -> failwith (Format.asprintf "unknown function %s" s)
    | CWrite (_, _) -> failwith "unimplemented CWrite"
    | CRef _ -> failwith "unimplemented CRef"
    | CRead _ -> failwith "unimplemented CRead"
    | CAssert (_, _) -> failwith "unimplemented CAssert"
    | CPerform (_, _) -> failwith "unimplemented CPerform"
    | CMatch (_, _, scr, None, [], cases) ->
      (* x :: xs -> e is represented as ("::", [x, xs], e) *)
      (* and constr_cases = (string * string list * core_lang) list *)
      Term.t_case (expr_to_why3 env scr)
        (List.map
           (fun (constr, args, body) ->
             let pat =
               match (constr, args) with
               | "::", [x; y] ->
                 let h =
                   Term.create_vsymbol (Ident.id_fresh x) (type_to_why3 env Int)
                 in
                 let t =
                   Term.create_vsymbol (Ident.id_fresh y)
                     (type_to_why3 env List_int)
                 in
                 (* TODO nested patterns not supported *)
                 Term.pat_app
                   Theories.(get_symbol list "Cons" env.theories)
                   [Term.pat_var h; Term.pat_var t]
                   (type_to_why3 env List_int)
               | "[]", [] ->
                 Term.pat_app
                   Theories.(get_symbol list "Nil" env.theories)
                   []
                   (type_to_why3 env List_int)
               | c, _ -> failwith (Format.asprintf "unhandled constr %s" c)
             in
             Term.t_close_branch pat (expr_to_why3 env body))
           cases)
    | CMatch (_, _, _, _, _, _) -> failwith "unimplemented effect CMatch"
    | CResume _ -> failwith "unimplemented CResume"
    | CLambda (_, _, _) -> failwith "unimplemented CLambda"
    | CShift _ | CReset _ -> failwith "TODO shift and reset expr_to_why3 "

  let pure_fn_to_logic_fn env pure_fn =
    let params =
      List.map (fun (p, t) -> (p, type_to_why3 env t)) pure_fn.pf_params
    in
    (* on first translation, we store the name *)
    let fn_name =
      match SMap.find_opt pure_fn.pf_name env.fn_names with
      | None ->
        let ls =
          Term.create_lsymbol
            (Ident.id_fresh pure_fn.pf_name)
            (List.map snd params)
            (Some (type_to_why3 env pure_fn.pf_ret_type))
        in
        env.fn_names <- SMap.add pure_fn.pf_name ls env.fn_names;
        (* failwith "asd"; *)
        ls
      | Some ls -> ls
    in
    let params =
      List.map
        (fun (v, t) -> (v, Term.create_vsymbol (Ident.id_fresh v) t))
        params
    in
    let params_l = List.map snd params in
    (* let params_m = SMap.of_list params in *)
    Decl.make_ls_defn fn_name params_l (expr_to_why3 env pure_fn.pf_body)

  let prove =
    let theories = Theories.create () in
    let task1 : Task.task = None in
    List.iter
      (fun t -> Theories.(needed t theories))
      Theories.[int; bool; list; extras];
    let task1 =
      Theories.fold
        (fun (_tid, why_th) task -> Task.use_export task why_th)
        theories task1
    in
    fun tenv qtf f ->
      let env =
        {
          tenv;
          theories = Theories.create ();
          forall = SMap.empty;
          fn_names = SMap.empty;
          exists = SMap.empty;
          letbound = SMap.empty;
        }
      in

      let quantified =
        qtf
        |> List.map (fun v ->
               let ty = SMap.find_opt v tenv |> Option.value ~default:Int in
               (v, Term.create_vsymbol (Ident.id_fresh v) (type_to_why3 env ty)))
        |> List.to_seq |> SMap.of_seq
      in

      (* set this before traversing the formula for real *)
      let env = { env with exists = quantified } in

      (* after pure functions are translated, so the names are in the env *)
      (* before adding theories to the task *)
      (* requires theories to build the formula *)
      let ass, goal = f env in

      (* let theories_needed =
           let ts =
             find_needed_theories#visit_pi () f
             :: List.map
                  (fun (_, v) -> find_needed_theories#visit_core_lang () v.pf_body)
                  (Globals.pure_fns ())
           in
           List.fold_right TSet.union ts TSet.empty
         in *)

      (* let int = (["int"], "Int")
         let bool = (["bool"], "Bool")
         let list = (["list"], "List")
         let extras = (["extras"], "Extras") *)

      (* set up task *)

      (* let task1 : Task.task = None in

         (* add theories to the task *)
         (* TODO with z3, somehow the builtin theory containing things like unit is not loaded unless at least one other theory is pulled in, so use the int theory every time for now *)
         (* use all theories. analyzing the formula for theories requires building it first, which is cyclic. this used to be broken by loading theories on demand, however *)
         List.iter
           (fun t -> Theories.(needed t env.theories))
           Theories.[int; bool; list; extras];
         (* Format.printf "initial@."; *)
         (* Theories.(needed int env.theories); *)
         (* TSet.iter (fun t -> Theories.needed t env.theories) theories_needed; *)
         let task1 =
           Theories.fold
             (fun (_tid, why_th) task ->
               (* Format.printf "theory added: %s@." (string_of_tid tid); *)
               Task.use_export task why_th)
             env.theories task1
         in *)

      (* handle names, which requires types, which means theories must be loaded by now *)
      (* let names =
           let vis = build_name_map env in
           SMap.merge_all_disjoint
             (vis#visit_pi () f
             :: List.map
                  (fun (_, v) -> vis#visit_core_lang () v.pf_body)
                  (Globals.pure_fns ()))
         in *)

      (* { initial with quantified } *)

      (* let env = create_env names tenv qtf in *)
      (* Format.printf "forall %s exists %s@."
         (string_of_list Fun.id (SMap.bindings env.forall |> List.map fst))
         (string_of_list Fun.id (SMap.bindings env.exists |> List.map fst)); *)

      (* let create_env names tenv qtf = *)

      (* add pure functions *)
      (* before adding theories to the task, as translation loads them *)
      (* Format.printf "adding pure fns@."; *)
      let task1 =
        let fns =
          List.map
            (fun (_k, v) ->
              (* Format.printf "translating %s@." _k; *)
              pure_fn_to_logic_fn env v)
            (Globals.pure_fns ()
            (* |> List.map (fun (name, fn) -> (name, Hipcore.Typedhip.Untypehip.untype_pure_fn_def fn)) *)
            )
        in
        match fns with [] -> task1 | _ :: _ -> Task.add_logic_decl task1 fns
      in

      (* Format.printf "task: %a@." Why3.Pretty.print_task task1; *)

      (* Format.printf "tenv: %s@." (Pretty.string_of_typ_env tenv); *)
      (* Format.printf "assumptions: %a@." Why3.Pretty.print_term ass; *)
      (* Format.printf "goal: %a@." Why3.Pretty.print_term goal; *)
      let monolithic_goal = true in
      let task1 =
        match monolithic_goal with
        | false ->
          (* add variables as parameters *)
          (* let task1 =
               List.fold_right
                 (fun (_k, v) t -> Task.add_param_decl t v)
                 (SMap.bindings env.names) task1
             in *)
          let task1 : Task.task =
            Task.add_prop_decl task1 Decl.Paxiom
              (Decl.create_prsymbol (Ident.id_fresh "ass1"))
              ass
          in
          let task1 : Task.task =
            Task.add_prop_decl task1 Decl.Pgoal
              (Decl.create_prsymbol (Ident.id_fresh "goal1"))
              goal
          in
          task1
        | true ->
          let overall =
            let ex =
              let ex = SMap.bindings env.exists |> List.map snd in
              Term.t_exists_close ex [] goal
            in
            let all = SMap.bindings env.forall |> List.map snd in
            Term.t_forall_close all [] (Term.t_implies ass ex)
          in
          let task1 : Task.task =
            (* Format.printf "%a@." Why3.Pretty.print_term overall; *)
            Task.add_prop_decl task1 Decl.Pgoal
              (Decl.create_prsymbol (Ident.id_fresh "goal1"))
              overall
          in
          task1
      in
      (* Format.printf "--- prove@."; *)
      attempt_proof task1
end

open Ptree
open Ptree_helpers

let rec type_to_whyml t =
  match t with
  | TyString -> PTtyapp (qualid ["String"; "string"], [])
  | Int -> PTtyapp (qualid ["Int"; "int"], [])
  | Unit -> PTtyapp (qualid ["tuple0"], [])
  | List_int ->
    PTtyapp (qualid ["List"; "list"], [PTtyapp (qualid ["Int"; "int"], [])])
  | Bool -> PTtyapp (qualid ["Bool"; "bool"], [])
  | Lamb -> PTtyapp (qualid ["Int"; "int"], [])
  | TVar _ -> PTtyapp (qualid ["Int"; "int"], [])
  | Arrow (t1, t2) -> PTarrow (type_to_whyml t1, type_to_whyml t2)
  | TConstr _ -> failwith "general ADTs not implemented"

let rec term_to_whyml tenv t =
  match t with
  | Const ValUnit -> term (Ttuple [])
  | Const TTrue -> term Ttrue
  | Const TFalse -> term Tfalse
  | Const (Num i) -> tconst i
  | Var v -> tvar (qualid [v])
  | BinOp (SConcat, a, b) ->
    tapp
      (qualid ["String"; "concat"])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | BinOp (Plus, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "+"])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | BinOp (Minus, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "-"])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | Rel (EQ, a, b) ->
    tapp
      (qualid [Ident.op_infix "="])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | Rel (GT, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix ">"])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | Rel (GTEQ, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix ">="])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | Rel (LT, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "<"])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | Rel (LTEQ, a, b) ->
    tapp
      (qualid ["Int"; Ident.op_infix "<="])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | BinOp (TAnd, a, b) ->
    tapp (qualid ["Bool"; "andb"]) [term_to_whyml tenv a; term_to_whyml tenv b]
  | BinOp (TOr, a, b) ->
    tapp (qualid ["Bool"; "orb"]) [term_to_whyml tenv a; term_to_whyml tenv b]
  | TNot a -> tapp (qualid ["Bool"; "notb"]) [term_to_whyml tenv a]
  | TApp (f, args) -> tapp (qualid [f]) (List.map (term_to_whyml tenv) args)
  | Const Nil -> tapp (qualid ["List"; "Nil"]) []
  | BinOp (TCons, h, t) ->
    tapp (qualid ["List"; "Cons"]) [term_to_whyml tenv h; term_to_whyml tenv t]
  | TLambda (_name, _, _sp, Some _) | TLambda (_name, _, _sp, None) ->
    (* if there is no body, generate something that only respects alpha equivalence *)
    (* this probably doesn't always work *)
    (* tconst (Subst.hash_lambda t) *)
    failwith "lambda"
  (* failwith "no body" *)
  (* disabled temporarily *)
  (* | TLambda (_name, params, _sp, Some body) ->
     let params, _ret = unsnoc params in
     let binders = vars_to_params tenv params in
     term (Tquant (Dterm.DTlambda, binders, [], core_lang_to_whyml tenv body)) *)
  | TTuple _ | BinOp (TPower, _, _) | BinOp (TTimes, _, _) | BinOp (TDiv, _, _) | Const (TStr _)
    ->
    failwith "nyi"

and vars_to_params tenv vars =
  List.map
    (fun v ->
      let type_of_existential =
        (* warning if default? *)
        SMap.find_opt v tenv |> Option.value ~default:Int
      in
      ( Loc.dummy_position,
        Some (ident v),
        false,
        Some (type_to_whyml type_of_existential) ))
    vars

and core_lang_to_whyml tenv e =
  match e with
  | CValue t -> term_to_whyml tenv t
  | CLet (v, e1, e2) ->
    term
      (Tlet (ident v, core_lang_to_whyml tenv e1, core_lang_to_whyml tenv e2))
  | CSequence (_e1, _e2) ->
      failwith "CSequence"
  | CIfELse (c, t, e) ->
    term
      (Tif
         ( pi_to_whyml tenv c,
           core_lang_to_whyml tenv t,
           core_lang_to_whyml tenv e ))
  | CFunCall (s, args) ->
    let fn =
      match s with
      | "+" | "-" | ">" | "<" | ">=" | "<=" -> qualid ["Int"; Ident.op_infix s]
      | "::" -> qualid ["List"; "Cons"]
      | "=" -> qualid ["Int"; Ident.op_infix s] (* for now *)
      | "||" -> qualid ["Bool"; "orb"]
      | "&&" -> qualid ["Bool"; "andb"]
      | "string_of_int" -> qualid ["String"; "from_int"]
      | _ -> qualid [s]
    in
    tapp fn (List.map (term_to_whyml tenv) args)
  | CMatch (_, None, scr, None, [], cases) ->
    term
      (Tcase
         ( core_lang_to_whyml tenv scr,
           List.map
             (fun (constr, args, b) ->
               let real_constr =
                 match constr with
                 | "[]" -> qualid ["List"; "Nil"]
                 | "::" -> qualid ["List"; "Cons"]
                 | _ -> failwith (Format.asprintf "unknown constr %s" constr)
               in
               ( pat
                   (Papp
                      (real_constr, List.map (fun a -> pat_var (ident a)) args)),
                 core_lang_to_whyml tenv b ))
             cases ))
  | CMatch (_, _, _, _, _, _) -> failwith "unsupported kind of match"
  | CAssert (_, _) | CLambda (_, _, _) -> failwith "unimplemented"
  | CWrite (_, _) | CRef _ | CRead _ -> failwith "heap operations not allowed"
  | CResume _ | CPerform (_, _) -> failwith "effects not allowed"
  | CShift _ | CReset _ -> failwith "TODO shift and reset core_lang_to_whyml "

and pi_to_whyml tenv p =
  match p with
  | True -> term Ttrue
  | False -> term Tfalse
  | Atomic (EQ, a, b) ->
    tapp
      (qualid [Ident.op_infix "="])
      [term_to_whyml tenv a; term_to_whyml tenv b]
  | Atomic (op, a, b) -> term_to_whyml tenv (Rel (op, a, b))
  | And (a, b) ->
    term (Tbinop (pi_to_whyml tenv a, Dterm.DTand, pi_to_whyml tenv b))
  | Or (a, b) ->
    term (Tbinop (pi_to_whyml tenv a, Dterm.DTor, pi_to_whyml tenv b))
  | Not a -> term (Tnot (pi_to_whyml tenv a))
  | Imply (_, _) | Predicate (_, _) -> failwith "nyi"
  | Subsumption (_, _) -> term Ttrue

let collect_variables =
  object
    inherit [_] reduce_spec
    method zero = SSet.empty
    method plus = SSet.union
    method! visit_Var _ v = SSet.singleton v

    (* don't go inside lambda, as those variables don't get encoded *)
    method! visit_TLambda _ _ _ _ _ = SSet.empty
  end

let prove tenv qtf f =
  let ass, goal = f () in

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
    let universally_quantified =
      SSet.union
        (collect_variables#visit_pi () ass)
        (collect_variables#visit_pi () goal)
      |> SSet.to_list
    in

    let statement =
      let assumptions = pi_to_whyml tenv ass in
      let goal1 =
        let binders = vars_to_params tenv qtf in
        match binders with
        | [] -> pi_to_whyml tenv goal
        | _ :: _ ->
          term (Tquant (Dterm.DTexists, binders, [], pi_to_whyml tenv goal))
      in
      match monolithic_goal with
      | false ->
        [
          Dprop (Decl.Paxiom, ident "ass1", pi_to_whyml tenv ass);
          Dprop (Decl.Pgoal, ident "goal1", goal1);
        ]
      | true ->
        let forall_binders = vars_to_params tenv universally_quantified in
        let impl = term (Tbinop (assumptions, Dterm.DTimplies, goal1)) in
        let goal2 =
          match forall_binders with
          | [] -> impl
          | _ :: _ -> term (Tquant (Dterm.DTforall, forall_binders, [], impl))
        in
        [Dprop (Decl.Pgoal, ident "goal1", goal2)]
    in

    let fns =
      match (Globals.pure_fns ()
      (* |> List.map (fun (name, fn) -> (name, Hipcore.Typedhip.Untypehip.untype_pure_fn_def fn)) *)
      ) with
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
                ld_def = Some (core_lang_to_whyml tenv fn.pf_body);
              })
            f
        in
        [Dlogic ff]
    in

    let parameters =
      match monolithic_goal with
      | true -> []
      | false ->
        [
          Dlogic
            (universally_quantified
            |> List.map (fun v ->
                   let type_of_parameter = SMap.find v tenv in
                   {
                     ld_loc = Loc.dummy_position;
                     ld_ident = ident v;
                     ld_params = [];
                     ld_type = Some (type_to_whyml type_of_parameter);
                     ld_def = None;
                   }));
        ]
    in

    let imports =
      let extra =
        Globals.global_environment.pure_fn_types
        (* |> SMap.map Hipcore.Typedhip.Untypehip.untype_pure_fn_type_def *)
        |> SMap.bindings
        |> List.map (fun (_, p) -> p.pft_logic_path)
        |> List.sort_uniq compare
        |> List.map (use ~import:false)
      in
      [
        use ~import:false ["int"; "Int"];
        use ~import:false ["bool"; "Bool"];
        use ~import:false ["list"; "List"];
      ]
      @ extra
    in
    (ident "M", List.concat [imports; fns; parameters; statement])
  in
  let mlw_file = Modules [vc_mod] in
  Debug.debug ~at:4 ~title:"mlw file" "%a"
    (Mlw_printer.pp_mlw_file ~attr:true)
    mlw_file;
  let mods =
    try Typing.type_mlw_file why3_env [] "myfile.mlw" mlw_file
    with Loc.Located (loc, e) ->
      (* A located exception [e] *)
      if Debug.in_debug_mode () then (
        Debug.debug ~at:4 ~title:"failed due to type error" "";
        let msg = Format.asprintf "%a" Exn_printer.exn_printer e in
        Format.printf "%a@."
          (Mlw_printer.with_marker ~msg loc
             (Mlw_printer.pp_mlw_file ~attr:true))
          mlw_file);
      failwith "failed due to type error"
  in
  (* there will be only one module *)
  Wstdlib.Mstr.fold
    (fun _ m acc ->
      let tasks = Task.split_theory m.Pmodule.mod_theory None None in
      List.for_all attempt_proof tasks && acc)
    mods true

let suppress_error_if_not_debug f =
  if Debug.in_debug_mode () then f ()
  else
    try f ()
    with e ->
      (* the stack trace printed is not the same (and is much less helpful) if the exception is caught *)
      Debug.debug ~at:1 ~title:"an error occurred, assuming proof failed" "%a"
        Exn_printer.exn_printer e;
      (* Printexc.print_backtrace stdout; *)
      false

(* Entry point to call why3 *)
let entails_exists tenv left ex right =
  let@ _ = Globals.Timing.(time why3) in
  let@ _ = suppress_error_if_not_debug in
  let use_low_level = false in
  match use_low_level with
  | false -> prove tenv ex (fun _env -> (left, right))
  | true ->
    (* keep this around for a while before we commit to the other approach *)
    let open LowLevel in
    prove tenv ex (fun env ->
        ( pi_to_why3 env left,
          (* Term.t_exists_close *)
          (* (SMap.bindings env.exists |> List.map snd) *)
          (* [] () *)
          pi_to_why3 env right ))
