open Hipcore
include Hiptypes

let handle f = f ()

open Why3

let prover_configs : Whyconf.config_prover SMap.t ref = ref SMap.empty
let prover_z3 = "Z3" 

(* top-level side effects *)
let why3_config = Whyconf.init_config None 
let why3_config_main = Whyconf.get_main why3_config
let why3_env : Env.env = Env.create_env (Whyconf.loadpath why3_config_main)

let load_prover_config name : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover name in
  let provers = Whyconf.filter_provers why3_config fp in
  if Whyconf.Mprover.is_empty provers then begin
    Format.eprintf "Prover %s not installed or not configured@." name;
    exit 1
  end
  else begin
    (* Format.printf "Versions of %s found:" name;
    Whyconf.(
      Mprover.iter
        (fun k _ -> Format.printf " %s/%s" k.prover_version k.prover_altern)
        provers);
    Format.printf "@."; *)
    (* returning an arbitrary one *)
    snd (Whyconf.Mprover.min_binding provers)
  end

let ensure_prover_loaded name =
  match SMap.find_opt name !prover_configs with
  | None -> prover_configs := SMap.add name (load_prover_config name) !prover_configs
  | Some _ -> ()

let get_prover_config name = SMap.find name !prover_configs

let load_prover_driver pc name =
  try Driver.load_driver_for_prover why3_config_main why3_env pc
  with e ->
    Format.eprintf "Failed to load driver for %s: %a@." name
      Exn_printer.exn_printer e;
      raise e



type env = {
  mutable names : Term.lsymbol SMap.t;
  int_theory : Theory.theory;
  tenv : typ SMap.t;
  quantified : Term.vsymbol SMap.t;
}


let type_to_why3 (t : typ) =
  match t with
  | Unit -> Ty.ty_tuple []
  | List_int -> failwith "nyi List_int"
  | Int -> Ty.ty_int
  | Bool -> Ty.ty_bool
  | Lamb -> failwith "nyi Lamb"
  | TVar _ -> Ty.ty_int (* default to int *)


let rec term_to_why3 env (t : term) =
  match t with
  | UNIT -> Term.t_tuple []
  | Num i -> Term.t_nat_const i
  | Var v ->
    let ty =
      SMap.find_opt v env.tenv |> Option.value ~default:Int |> type_to_why3
    in
    let name =
      match SMap.find_opt v env.quantified with
      | Some v -> Term.t_var v
      | None ->
        match SMap.find_opt v env.names with
        | None ->
          let name = Ident.id_fresh v in
          let sym = Term.create_lsymbol name [] (Some ty) in
          env.names <- SMap.add v sym env.names;
          Term.t_app sym [] (Some ty)
        | Some vv -> Term.t_app vv [] (Some ty)
    in
    name
  | Plus (a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix +"])
      [term_to_why3 env a; term_to_why3 env b]
  | Minus (a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix -"])
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (EQ, a, b) -> Term.t_equ (term_to_why3 env a) (term_to_why3 env b)
  | Rel (GT, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix >"])
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (LT, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix <"])
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (GTEQ, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix >="])
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (LTEQ, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix <="])
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
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix >"])
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (LT, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix <"])
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (GTEQ, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix >="])
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (LTEQ, a, b) ->
    Term.t_app_infer
      (Theory.ns_find_ls env.int_theory.Theory.th_export ["infix <="])
      [term_to_why3 env a; term_to_why3 env b]
  | And (a, b) -> Term.t_and (pi_to_why3 env a) (pi_to_why3 env b)
  | Or (a, b) -> Term.t_or (pi_to_why3 env a) (pi_to_why3 env b)
  | Imply (a, b) -> Term.t_implies (pi_to_why3 env a) (pi_to_why3 env b)
  | Not a -> Term.t_not (pi_to_why3 env a)
  | Predicate (_, _) -> failwith "nyi Predicate"

let create_env tenv qtf =
  let int_theory = Env.read_theory why3_env ["int"] "Int" in
  let quantified =
    qtf
      |> List.map (fun v ->
        let ty = SMap.find_opt v tenv |> Option.value ~default:Int in
        v, Term.create_vsymbol (Ident.id_fresh v) (type_to_why3 ty))
      |> List.to_seq
      |> SMap.of_seq
  in
  { int_theory; names = SMap.empty; tenv; quantified }


let prove tenv qtf f =
  let env = create_env tenv qtf in
  let ass, goal = f env in

  (* set up task *)
  let task1 : Task.task = None in
  let task1 = Task.use_export task1 env.int_theory in
  (* let debug = true in *)
  let debug = false in

  let task1 =
    List.fold_right
      (fun (_k, v) t -> Task.add_param_decl t v)
      (SMap.bindings env.names) task1
  in

  if debug then
    Format.printf "assumptions: %a@." Pretty.print_term ass;
  if debug then
    Format.printf "goal: %a@." Pretty.print_term goal;
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
  ensure_prover_loaded prover_z3;
  let pc = get_prover_config prover_z3 in
  let result1 =
    Call_provers.wait_on_call
      (Driver.prove_task ~limit:Call_provers.empty_limit ~config:why3_config_main
         ~command:pc.Whyconf.command (load_prover_driver pc prover_z3) task1)
  in
  if debug then
    Format.printf "%s: %a@." "Z3"
      (Call_provers.print_prover_result ?json:None)
      result1;
  match result1.pr_answer with Valid -> true | _ -> false

let entails_exists tenv left ex right =
  prove tenv ex (fun env ->
      (pi_to_why3 env left,
        Term.t_exists_close (SMap.bindings env.quantified |> List.map snd) [] (pi_to_why3 env right)))
