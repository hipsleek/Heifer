open Hipcore
include Hiptypes

let handle f = f ()

open Why3

(* let fmla1 : Term.term = Term.t_or Term.t_true Term.t_false
let prop_var_A : Term.lsymbol = Term.create_psymbol (Ident.id_fresh "A") []
let prop_var_B : Term.lsymbol = Term.create_psymbol (Ident.id_fresh "B") []
let atom_A : Term.term = Term.ps_app prop_var_A []
let atom_B : Term.term = Term.ps_app prop_var_B []
let fmla2 : Term.term = Term.t_implies (Term.t_and atom_A atom_B) atom_A *)

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
  | Var _ -> failwith "Var nyi"
  | Plus (a, b) ->
    let plus_symbol : Term.lsymbol =
      Theory.ns_find_ls (use_int_theory env).Theory.th_export ["infix +"]
    in
    Term.t_app_infer plus_symbol [term_to_why3 env a; term_to_why3 env b]
  | Minus (_, _) -> failwith "Minus nyi"
  | Rel (_, _, _) -> failwith "Rel nyi"
  | TTrue -> failwith "TTrue nyi"
  | TFalse -> failwith "TFalse nyi"
  | TAnd (_, _) -> failwith "TAnd nyi"
  | TPower (_, _) -> failwith "TPower nyi"
  | TTimes (_, _) -> failwith "TTimes nyi"
  | TDiv (_, _) -> failwith "TDiv nyi"
  | TOr (_, _) -> failwith "TOr nyi"
  | TNot _ -> failwith "TNot nyi"
  | TApp (_, _) -> failwith "TApp nyi"
  | Nil -> failwith "Nil nyi"
  | TLambda (_, _, _) -> failwith "TLambda nyi"
  | TList _ -> failwith "TList nyi"
  | TTupple _ -> failwith "TTupple nyi"

let rec pi_to_why3 env (pi : pi) =
  match pi with
  | True -> Term.t_true
  | False -> Term.t_false
  | Atomic (EQ, a, b) -> Term.t_equ (term_to_why3 env a) (term_to_why3 env b)
  | Atomic (GT, a, b) -> Term.t_equ (term_to_why3 env a) (term_to_why3 env b)
  | Atomic (LT, a, b) -> Term.t_equ (term_to_why3 env a) (term_to_why3 env b)
  | Atomic (GTEQ, a, b) -> Term.t_equ (term_to_why3 env a) (term_to_why3 env b)
  | Atomic (LTEQ, a, b) -> Term.t_equ (term_to_why3 env a) (term_to_why3 env b)
  | And (a, b) -> Term.t_and (pi_to_why3 env a) (pi_to_why3 env b)
  | Or (_, _) -> failwith "nyi Or"
  | Imply (_, _) -> failwith "nyi Imply"
  | Not _ -> failwith "nyi Not"
  | Predicate (_, _) -> failwith "nyi Predicate"

let prove f goal =
  (* reads the default config file *)
  let config : Whyconf.config = Whyconf.init_config None in
  (* the [main] section of the config file *)
  let main : Whyconf.main = Whyconf.get_main config in
  (* builds the environment from the [loadpath] *)
  let env : Env.env = Env.create_env (Whyconf.loadpath main) in

  (* Format.printf "proving@."; *)
  (* Format.printf "load path: %s@." (string_of_list Fun.id (Whyconf.loadpath main)); *)
  let env = create_env env in
  let ggoal = f env goal in

  (* set up task *)
  let task1 : Task.task = None in
  (* let task1 = Task.use_export task1 env.int_theory in *)
  let task1 = apply_exports env task1 in
  let goal_id1 : Decl.prsymbol =
    Decl.create_prsymbol (Ident.id_fresh "goal1")
  in
  let task1 : Task.task = Task.add_prop_decl task1 Decl.Pgoal goal_id1 ggoal in
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
  match result1.pr_answer with
  | Valid -> true
  | _ -> false

let entails_exists _env _left _ex _right =
  (* Format.printf "@[formula 2 is:@ %a@]@." Pretty.print_term fmla2; *)
  (* Format.printf "@[formula 1 is:@ %a@]@." Pretty.print_term fmla1; *)
  (* prove (fun _ f -> f) fmla1; *)
  let right = Atomic (EQ, Plus (Num 1, Num 1), Num 2) in
  prove pi_to_why3 right