open Hipcore
open Hiptypes

(* let debug = true *)
let debug = false

open Why3

let prover_configs : Whyconf.config_prover SMap.t ref = ref SMap.empty

(* top-level side effects *)
let why3_config = Whyconf.init_config None
let why3_config_main = Whyconf.get_main why3_config
let why3_env : Env.env = Env.create_env (Whyconf.loadpath why3_config_main)

let load_prover_config name : Whyconf.config_prover =
  let fp = Whyconf.parse_filter_prover name in
  let provers = Whyconf.filter_provers why3_config fp in
  if Whyconf.Mprover.is_empty provers then begin
    Format.printf "Prover %s not installed or not configured@." name;
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
  | None ->
    prover_configs := SMap.add name (load_prover_config name) !prover_configs
  | Some _ -> ()

let get_prover_config name = SMap.find name !prover_configs

let load_prover_driver pc name =
  try Driver.load_driver_for_prover why3_config_main why3_env pc
  with e ->
    Format.printf "Failed to load driver for %s: %a@." name
      Exn_printer.exn_printer e;
    raise e

(** Mutable data structure for keeping track of which theories have been loaded *)
module Theories = struct
  module TMap = Map.Make (struct
    type t = string list * string

    let compare = compare
  end)

  type t = Theory.theory TMap.t ref

  let create () = ref TMap.empty
  let fold f t init = List.fold_right f (TMap.bindings !t) init

  (* Some common ones we use *)
  let int = (["int"], "Int")
  let bool = (["bool"], "Bool")
  let list = (["list"], "List")

  let needed tid t =
    match TMap.find_opt tid !t with
    | None ->
      let path, name = tid in
      t := TMap.add tid (Env.read_theory why3_env path name) !t
    | Some _ -> ()

  let get_symbol th sym t =
    match TMap.find_opt th !t with
    | None -> failwith (Format.asprintf "theory with symbol %s not loaded" sym)
    | Some t -> Theory.ns_find_ls t.Theory.th_export [sym]

  let get_type_symbol th sym t =
    match TMap.find_opt th !t with
    | None ->
      failwith (Format.asprintf "theory with type symbol %s not loaded" sym)
    | Some t -> Theory.ns_find_ts t.Theory.th_export [sym]
end

type env = {
  mutable names : Term.lsymbol SMap.t;
  theories : Theories.t; (* TODO consider making this global for performance *)
  tenv : typ SMap.t;
  quantified : Term.vsymbol SMap.t;
}

let type_to_why3 env (t : typ) =
  match t with
  | Unit -> Ty.ty_tuple []
  | List_int ->
    Theories.(needed int env.theories);
    Theories.(needed list env.theories);
    Ty.ty_app Theories.(get_type_symbol list "list" env.theories) [Ty.ty_int]
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

let rec term_to_why3 env (t : term) =
  if debug then Format.printf "term %s@." (Hipcore.Pretty.string_of_term t);
  match t with
  | UNIT -> Term.t_tuple []
  | Num i ->
    Theories.(needed int env.theories);
    Term.t_nat_const i
  | TLambda (_, _, _) ->
    Theories.(needed int env.theories);
    Term.t_nat_const (Hipcore.Subst.hash_lambda t)
  | Var v ->
    let ty =
      SMap.find_opt v env.tenv |> Option.value ~default:Int |> type_to_why3 env
    in
    let name =
      match SMap.find_opt v env.quantified with
      | Some v -> Term.t_var v
      | None ->
        (match SMap.find_opt v env.names with
        | None ->
          let name = Ident.id_fresh v in
          let sym = Term.create_lsymbol name [] (Some ty) in
          env.names <- SMap.add v sym env.names;
          Term.t_app sym [] (Some ty)
        | Some vv -> Term.t_app vv [] (Some ty))
    in
    (* Format.printf "var %s : %s@." v
       Hipcore.Pretty.(
         string_of_option string_of_type (SMap.find_opt v env.tenv)); *)
    name
  | Plus (a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix +" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | Minus (a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix -" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (EQ, a, b) ->
    let a1 = term_to_why3 env a in
    let b1 = term_to_why3 env b in
    Term.t_equ a1 b1
  | Rel (GT, a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix >" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (LT, a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix <" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (GTEQ, a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix >=" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | Rel (LTEQ, a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix <=" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | TTrue ->
    Theories.(needed bool env.theories);
    Term.t_bool_true
  | TFalse ->
    Theories.(needed bool env.theories);
    Term.t_bool_false
  | TAnd (a, b) ->
    Theories.(needed bool env.theories);
    Term.t_app_infer
      Theories.(get_symbol bool "andb" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
    (* Term.fs_app  [] Ty.ty_bool *)
    (* Term.t_and (term_to_why3 env a) (term_to_why3 env b) *)
  | TOr (a, b) ->
    (* Term.t_and (term_to_why3 env a) (term_to_why3 env b) *)
    Theories.(needed bool env.theories);
    Term.t_app_infer
      Theories.(get_symbol bool "orb" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | TNot a ->
    (* Term.t_not (term_to_why3 env a) *)
    Theories.(needed bool env.theories);
    Term.t_app_infer
      Theories.(get_symbol bool "notb" env.theories)
      [term_to_why3 env a]
  | TCons (a, b) ->
    (* let open Hipcore.Pretty in *)
    (* Format.printf "cons %s %s @." (string_of_term a) (string_of_term b); *)
    Term.t_app
      Theories.(get_symbol list "Cons" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
      (Some (type_to_why3 env List_int))
    (* inferring types leads to issues reconciling types between systems *)
    (* Term.t_app_infer
       (get_theory_symbol env.list_theory "Cons")
       [term_to_why3 env a; term_to_why3 env b] *)
  | Nil ->
    (* Term.t_app_infer (get_theory_symbol env.list_theory "Nil") [] *)
    Term.t_app
      Theories.(get_symbol list "Nil" env.theories)
      []
      (Some (type_to_why3 env List_int))
  | TApp (s, _) -> failwith (Format.asprintf "TApp nyi %s" s)
  | TPower (_, _) -> failwith "TPower nyi"
  | TTimes (_, _) -> failwith "TTimes nyi"
  | TDiv (_, _) -> failwith "TDiv nyi"
  | TList _ -> failwith "TList nyi"
  | TTupple _ -> failwith "TTupple nyi"

let rec pi_to_why3 env (pi : pi) =
  if debug then Format.printf "pi %s@." (Hipcore.Pretty.string_of_pi pi);
  match pi with
  | True -> Term.t_true
  | False -> Term.t_false
  | Atomic (EQ, a, b) ->
    let a1 = term_to_why3 env a in
    let b1 = term_to_why3 env b in
    Term.t_equ a1 b1
  | Atomic (GT, a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix >" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (LT, a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix <" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (GTEQ, a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix >=" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | Atomic (LTEQ, a, b) ->
    Theories.(needed int env.theories);
    Term.t_app_infer
      Theories.(get_symbol int "infix <=" env.theories)
      [term_to_why3 env a; term_to_why3 env b]
  | And (a, b) -> Term.t_and (pi_to_why3 env a) (pi_to_why3 env b)
  | Or (a, b) -> Term.t_or (pi_to_why3 env a) (pi_to_why3 env b)
  | Imply (a, b) -> Term.t_implies (pi_to_why3 env a) (pi_to_why3 env b)
  | Not a -> Term.t_not (pi_to_why3 env a)
  | IsDatatype (v, typ, constr, args) ->
    let v1 = term_to_why3 env v in
    let args1 = List.map (term_to_why3 env) args in
    let rhs =
      let tsym =
        match (typ, constr) with
        | "list", "cons" -> Theories.(get_symbol list "Cons" env.theories)
        | _ ->
          failwith
            (Format.asprintf "unknown type and constr: %s, %s" typ constr)
      in
      Term.t_app tsym args1 (Some (type_to_why3 env List_int))
    in
    Term.t_equ v1 rhs
  | Predicate (_, _) -> failwith "nyi Predicate"

let create_env tenv qtf =
  let initial =
    {
      names = SMap.empty;
      tenv;
      quantified = SMap.empty;
      theories = Theories.create ();
    }
  in
  let quantified =
    qtf
    |> List.map (fun v ->
           let ty = SMap.find_opt v tenv |> Option.value ~default:Int in
           (v, Term.create_vsymbol (Ident.id_fresh v) (type_to_why3 initial ty)))
    |> List.to_seq |> SMap.of_seq
  in
  { initial with quantified }

let attempt_proof task1 =
  (* if debug then Format.printf "task: %a@." Pretty.print_task task1; *)
  let prover_z3 = "Z3" in
  let prover_alt_ergo = "Alt-Ergo" in
  [prover_alt_ergo; prover_z3]
  |> List.exists (fun prover ->
         ensure_prover_loaded prover;
         let pc = get_prover_config prover in
         let driver = load_prover_driver pc prover in
         let result1 =
           Call_provers.wait_on_call
             (Driver.prove_task
                ~limit:
                  {
                    Call_provers.empty_limit with
                    Call_provers.limit_time = 0.5;
                  }
                ~config:why3_config_main ~command:pc.Whyconf.command driver
                task1)
         in
         if debug then
           Format.printf "%s: %a@." prover
             (Call_provers.print_prover_result ?json:None)
             result1;
         match result1.pr_answer with Valid -> true | _ -> false)

let prove tenv qtf f =
  let env = create_env tenv qtf in
  let ass, goal = f env in

  (* set up task *)
  let task1 : Task.task = None in

  (* with z3, somehow the builtin theory containing things like unit is not loaded unless at least one other theory is pulled in, so use the int theory every time for now *)
  Theories.(needed int env.theories);

  (* make loaded theories available *)
  let task1 =
    Theories.fold
      (fun (_tid, why_th) task -> Task.use_export task why_th)
      env.theories task1
  in

  (* Format.printf "task: %a@." Pretty.print_task task1; *)
  let task1 =
    List.fold_right
      (fun (_k, v) t -> Task.add_param_decl t v)
      (SMap.bindings env.names) task1
  in

  (* if debug then *)
  (* Format.printf "tenv: %s@." (Hipcore.Pretty.string_of_typ_env tenv); *)
  if debug then Format.printf "assumptions: %a@." Pretty.print_term ass;
  if debug then Format.printf "goal: %a@." Pretty.print_term goal;
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
  attempt_proof task1

let cache : (pi * string list * pi, bool) Hashtbl.t = Hashtbl.create 10

let memo k f =
  match Hashtbl.find_opt cache k with
  | None ->
    let r = f () in
    Hashtbl.add cache k r;
    r
  | Some r -> r

let entails_exists tenv left ex right =
  let@ _ = memo (left, ex, right) in
  let f () =
    prove tenv ex (fun env ->
        ( pi_to_why3 env left,
          Term.t_exists_close
            (SMap.bindings env.quantified |> List.map snd)
            [] (pi_to_why3 env right) ))
  in
  if debug then f ()
  else
    try f ()
    with e ->
      (* the stack trace printed is not the same (and is much less helpful) if the exception is caught, hence the use of the debug flag *)
      Format.printf "an error occurred, assuming proof failed: %a@."
        Exn_printer.exn_printer e;
      (* Printexc.print_backtrace stdout; *)
      false
