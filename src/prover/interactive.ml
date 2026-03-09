open Core.Syntax
open Core.Decl
open Core.Syntax_util
open Util.Strings
open Tactics

module State = struct
  type mode =
    | Mode_lemma of string * term
    | Mode_goal
    | Mode_none

  type t = {
    definitions : symbol_table;
    lemmas : term SMap.t;
    mode : mode;
    goals : Pstate.t;
  }

  let initial_state =
    { definitions = empty_table; lemmas = SMap.empty; mode = Mode_none; goals = [] }

  let state_stack = ref []
  let current_state = ref initial_state
  let reset_proof_state () = current_state := initial_state
  let print_proof_state () = Format.printf "%a@." Pstate.pp !current_state.goals
  let push_proof_state () = state_stack := !current_state :: !state_stack

  let pop_proof_state () =
    match !state_stack with
    | [] -> Format.printf "state stack is empty@."
    | state :: stack ->
        current_state := state;
        state_stack := stack

  let get_definitions () = !current_state.definitions
  let get_lemmas () = !current_state.lemmas
  let get_mode () = !current_state.mode
  let get_goals () = !current_state.goals
  let set_definitions definitions = current_state := { !current_state with definitions }
  let set_lemmas lemmas = current_state := { !current_state with lemmas }
  let set_mode mode = current_state := { !current_state with mode }
  let set_goals goals = current_state := { !current_state with goals }
  let set_goal goal = set_goals [goal]
  let add_goals goals = set_goals (goals @ get_goals ())
  let add_lemma name term = set_lemmas (SMap.add name term (get_lemmas ()))
  let get_lemma_opt name = SMap.find_opt name (get_lemmas ())
  let get_definition_opt sym = SymMap.find_opt sym (get_definitions ())

  let declare_defn sym def =
    set_definitions (add_decl sym def !current_state.definitions);
    Format.printf "%s declared@." sym.sym_name

  let declare decl =
    let sym, def = open_dfun (Parsing.Parse.parse_decl decl) in
    declare_defn sym def

  let axiom ~name term =
    let goal = Parsing.Parse.parse_term term in
    add_lemma name goal;
    Format.printf "axiom %s declared@." name

  let lemma ~name term =
    let goal = Parsing.Parse.parse_term term in
    set_mode (Mode_lemma (name, goal));
    set_goal (Pctx.create goal);
    print_proof_state ()

  let start_proof term =
    let goal = Parsing.Parse.parse_term term in
    set_mode Mode_goal;
    set_goal (Pctx.create goal);
    print_proof_state ()

  let run_tactic tactic =
    match Tactic.run_pstate tactic (get_goals ()) with
    | Ok new_goals ->
        set_goals new_goals;
        print_proof_state ()
    | Error msg ->
        Format.printf "error: %s@." msg;
        if !Prover_options.fail_fast then failwith msg

  let run tactic =
    match Tactic.run tactic (get_goals ()) with
    | Ok (result, new_goals) ->
        set_goals new_goals;
        print_proof_state ();
        Some result
    | Error msg ->
        Format.printf "error: %s@." msg;
        if !Prover_options.fail_fast then failwith msg else None

  let make_interactive (tac : 'b -> 'a Tactic.t) (arg : 'b) = run_tactic (tac arg)

  let when_goal_is_empty f =
    if Pstate.is_empty (get_goals ()) then f () else Format.printf "error: proof is still open@."

  let qed () =
    match get_mode () with
    | Mode_goal -> when_goal_is_empty (fun () -> set_mode Mode_none)
    | Mode_lemma (name, goal) ->
        when_goal_is_empty (fun () ->
            add_lemma name goal;
            set_mode Mode_none;
            Format.printf "lemma %s declared@." name)
    | Mode_none -> Format.printf "error: no open proof@."
end

open State

let have ~name = make_interactive (have ~name)
let case ~name = make_interactive (case ~name)
let goal_is term = run_tactic (goal_is term)
let specialize h = make_interactive (specialize h)
let forward = make_interactive forward
let refl () = run_tactic refl
let funext () = run_tactic funext
let congruence () = run_tactic congruence
let req_heap_intro () = run_tactic Heaps.req_heap_intro
let ens_heap_elim () = run_tactic Heaps.ens_heap_elim
let req_heap_elim () = run_tactic Heaps.req_heap_elim
let ens_heap_intro () = run_tactic Heaps.ens_heap_intro
let req_pure_intro name = run_tactic (Pures.req_pure_intro name)
let req_pure_elim () = run_tactic Pures.req_pure_elim
let ens_pure_intro () = run_tactic Pures.ens_pure_intro
let ens_pure_elim name = run_tactic (Pures.ens_pure_elim name)
let intro_pure name = run_tactic (Pures.intro_pure name)
let elim_pure () = run_tactic Pures.elim_pure
let intro_heap () = run_tactic Heaps.intro_heap
let intros_heap () = run_tactic Heaps.intros_heap
let elim_heap () = run_tactic Heaps.elim_heap
let revert name = run_tactic (revert name)
let revert_pure name = run_tactic (Pures.revert_pure name)
let clear_pure name = run_tactic (Pures.clear_pure name)
let pure_solver () = run_tactic Pures.pure_solver
let revert_heap ?(side = `Lhs) () = run_tactic (Heaps.revert_heap ~side)
let heap_solver () = run_tactic Heaps.heap_solver
let forall_intro () = run_tactic forall_intro
let forall_elim ts = run_tactic (forall_elim ts)
let exists_intro ts = run_tactic (exists_intro ts)
let exists_elim () = run_tactic exists_elim
let conj_elim_l () = run_tactic Conj.conj_elim_l
let conj_elim_r () = run_tactic Conj.conj_elim_r
let disj_elim () = run_tactic Disj.disj_elim
let left () = run_tactic Disj.left
let right () = run_tactic Disj.right
let simpl_beta () = run_tactic Simpl.simpl_beta
let simpl () = run_tactic Simpl.simpl
let shift_reset_reduce () = run_tactic Simpl.shift_reset_reduce
let unmix () = run_tactic Unmix.unmix
let ex_falso () = run_tactic ex_falso
let prove () = run_tactic prove
let admit () = run_tactic admit
let prove_s s = Why3_prover.prove ~show_goal:true (Parsing.Parse.parse_prop s)

(* let simple () = run_tactic Automation.simple *)
let simple () = run_tactic (Automation.simple ~lemmas:(SMap.bindings (get_lemmas ())))
let simple2 () = run (Automation.solve_cert ~lemmas:(SMap.bindings (get_lemmas ())))
let dbg_simple () = run_tactic (Automation.dbg_simple ~lemmas:(SMap.bindings (get_lemmas ())))

(** Unfold a definition (symbol) on both side of a sequent in the current proof state. *)
let unfold ?(side = `Both) name =
  let tactic =
    let open Tactic in
    let sym = { sym_name = name } in
    match get_definition_opt sym with
    | None -> failf "unfold: %s does not exist" name
    | Some def ->
        let f_modify =
          match side with
          | `Lhs -> modify_lhs
          | `Rhs -> modify_rhs
          | `Both -> modify_goal
        in
        f_modify (Unfold.unfold sym def)
  in
  run_tactic tactic

(** Generate an induction hypothesis in the current proof state. *)
let induction :
    ?vars:string list -> name:string -> [ `Regex | `List | `Int of int ] -> string -> unit =
 fun ?(vars = []) ~name kind x -> run_tactic (induction ~vars ~name kind x)

let interactive_get_assumption name =
  let open Tactic in
  catch (get_assumption name) (fun _ ->
      match get_lemma_opt name with
      | Some assumption -> pure assumption
      | None -> failf "%s does not exist" name)

let rewrite ?(direction = `Ltr) name =
  let open Tactic in
  run_tactic (interactive_get_assumption name >>= rewrite ~direction)
