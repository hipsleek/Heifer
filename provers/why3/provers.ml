open Hipcore
include Hiptypes

let handle f = f ()

open Why3

type env = {
  mutable int_theory : Theory.theory option;
  env : Env.env;
}

let create_env env = { int_theory = None; env }

let use_int_theory env =
  match env.int_theory with
  | None ->
    let t = Env.read_theory env.env ["int"] "Int" in
    env.int_theory <- Some t;
    t
  | Some t -> t

let apply_exports env task1 =
  match env.int_theory with None -> task1 | Some t -> Task.use_export task1 t

let get_prover config name : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover name in
  let provers = Whyconf.filter_provers config fp in
  if Whyconf.Mprover.is_empty provers then begin
    Format.eprintf "Prover %s not installed or not configured@." name;
    exit 1
  end
  else begin
    Format.printf "Versions of %s found:" name;
    Whyconf.(
      Mprover.iter
        (fun k _ -> Format.printf " %s/%s" k.prover_version k.prover_altern)
        provers);
    Format.printf "@.";
    (* returning an arbitrary one *)
    snd (Whyconf.Mprover.min_binding provers)
  end

let rec term_to_why3 env (t : term) =
  match t with
  | UNIT -> failwith "UNIT nyi"
  | Num i -> Term.t_nat_const i (* Term.t_int_const (BigInt.of_int i) *)
  | Var v ->
    let s : Term.lsymbol = Term.create_psymbol (Ident.id_fresh v) [] in
    Term.ps_app s []
  | Plus (a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix +"])
      [term_to_why3 env a; term_to_why3 env b]
  | Minus (a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix -"])
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (EQ, a, b) -> Term.t_equ (term_to_why3 env a) (term_to_why3 env b)
  | Rel (GT, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix >"])
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (LT, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix <"])
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (GTEQ, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix >="])
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (LTEQ, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix <="])
      [term_to_why3 env a; term_to_why3 env b]
  | TTrue -> Term.t_true
  | TFalse -> Term.t_false
  | TAnd (a, b) -> Term.t_and (term_to_why3 env a) (term_to_why3 env b)
  | TOr (a, b) -> Term.t_and (term_to_why3 env a) (term_to_why3 env b)
  | TNot a -> Term.t_not (term_to_why3 env a)
  | TApp (_, _) -> failwith "TApp nyi"
  | Nil -> failwith "Nil nyi"
  | TLambda (_, _, _) -> failwith "TLambda nyi"
  | TPower (_, _) -> failwith "TPower nyi"
  | TTimes (_, _) -> failwith "TTimes nyi"
  | TDiv (_, _) -> failwith "TDiv nyi"
  | TList _ -> failwith "TList nyi"
  | TTupple _ -> failwith "TTupple nyi"

let rec pi_to_why3 env (pi : pi) =
  match pi with
  | True -> Term.t_true
  | False -> Term.t_false
  | Atomic (EQ, a, b) -> Term.t_equ (term_to_why3 env a) (term_to_why3 env b)
  | Atomic (GT, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix >"])
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (LT, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix <"])
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (GTEQ, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix >="])
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (LTEQ, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix <="])
      [term_to_why3 env a; term_to_why3 env b]
  | And (a, b) -> Term.t_and (pi_to_why3 env a) (pi_to_why3 env b)
  | Or (a, b) -> Term.t_or (pi_to_why3 env a) (pi_to_why3 env b)
  | Imply (a, b) -> Term.t_implies (pi_to_why3 env a) (pi_to_why3 env b)
  | Not a -> Term.t_not (pi_to_why3 env a)
  | Predicate (_, _) -> failwith "nyi Predicate"

let prove f =
  (* reads the default config file *)
  let config : Whyconf.config = Whyconf.init_config None in
  (* the [main] section of the config file *)
  let main : Whyconf.main = Whyconf.get_main config in
  (* builds the environment from the [loadpath] *)
  let env : Env.env = Env.create_env (Whyconf.loadpath main) in

  (* Format.printf "proving@."; *)
  (* Format.printf "load path: %s@." (string_of_list Fun.id (Whyconf.loadpath main)); *)
  let env = create_env env in
  let ass, goal = f env in

  (* set up task *)
  let task1 : Task.task = None in
  (* let task1 = Task.use_export task1 env.int_theory in *)
  let task1 = apply_exports env task1 in
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
  (* Format.printf "@[task 1 is:@\n%a@]@." Pretty.print_task task1; *)
  (* all the provers detected, from the config file *)
  (* let provers : Whyconf.config_prover Whyconf.Mprover.t = *)
  (* Whyconf.get_provers config in *)
  let prover_name = "Z3" in
  let z3 = get_prover config prover_name in
  let driver : Driver.driver =
    try Driver.load_driver_for_prover main env.env z3
    with e ->
      Format.eprintf "Failed to load driver for %s: %a@." prover_name
        Exn_printer.exn_printer e;
      exit 1
  in
  let result1 : Call_provers.prover_result =
    Call_provers.wait_on_call
      (Driver.prove_task ~limit:Call_provers.empty_limit ~config:main
         ~command:z3.Whyconf.command driver task1)
  in
  Format.printf "%s: %a@." prover_name
    (Call_provers.print_prover_result ?json:None)
    result1;
  match result1.pr_answer with Valid -> true | _ -> false

let type_to_why3 (t : typ) =
  match t with
  | Unit -> failwith "nyi Unit"
  | List_int -> failwith "nyi List_int"
  | Int -> Ty.ty_int
  | Bool -> Ty.ty_bool
  | Lamb -> failwith "nyi Lamb"
  | TVar _ -> failwith "nyi TVar"

let entails_exists tenv left ex right =
  (* Format.printf "@[formula 2 is:@ %a@]@." Pretty.print_term fmla2; *)
  (* Format.printf "@[formula 1 is:@ %a@]@." Pretty.print_term fmla1; *)
  (* prove (fun _ f -> f) fmla1; *)
  (* let right = Atomic (EQ, Plus (Num 1, Num 1), Num 2) in *)
  let vars =
    List.map
      (fun v ->
        let ty = SMap.find_opt v tenv |> Option.value ~default:Int in
        Term.create_vsymbol (Ident.id_fresh "x") (type_to_why3 ty))
      ex
  in
  prove (fun env ->
      (pi_to_why3 env left, Term.t_exists_close vars [] (pi_to_why3 env right)))
