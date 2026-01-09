open Core.Syntax
open Core.Pretty
open Core.Decl
open Core.Syntax_util
open Parsing.Parse
open Bindlib

module SMap = struct
  include Map.Make (String)

  let pp ~pp_k ~pp_v ppf m =
    let al = bindings m in
    Fmt.pf ppf "@[<hov>{%a}@]"
      Fmt.(list ~sep:(any ",@ ") (pair ~sep:(any ":@ ") pp_k pp_v))
      al
end

let pp_hypotheses ~pp_k ~pp_v ppf m =
  let al = SMap.bindings m in
  Fmt.pf ppf "@[<v>%a@]"
    Fmt.(
      list ~sep:(any "@,")
        (Fmt.hovbox ~indent:2 (pair ~sep:(any ":@ ") pp_k pp_v)))
    al

type sequent = staged_spec * staged_spec

module Pctx = struct
  type t = {
    rename_ctxt : Bindlib.ctxt;
    constants : term var SMap.t;
    assumptions : prop SMap.t;
    heap_context : hprop list;
    goal : sequent;
  }

  let create ~goal () =
    {
      rename_ctxt = empty_ctxt;
      (* simple solution for now. *)
      constants = SMap.empty;
      assumptions = SMap.empty;
      heap_context = [];
      goal;
    }

  let draw_line n = String.make n '-'

  (* TODO: use rename_ctxt *)
  let pp ppf
      { rename_ctxt = _; constants; assumptions; heap_context; goal = l, r } =
    Format.open_vbox 0;
    Fmt.pf ppf "@[<hov>%a@]@,"
      Fmt.(list ~sep:comma Fmt.string)
      (List.map fst (SMap.bindings constants));
    (match SMap.is_empty assumptions with
    | true -> ()
    | false ->
      Fmt.pf ppf "%a@,"
        (pp_hypotheses ~pp_k:Fmt.string ~pp_v:pp_prop)
        assumptions);
    (* always draw the line, even if there are no hypotheses *)
    let line_length = 40 in
    let line = draw_line line_length in
    Fmt.pf ppf "%s@," line;
    (match heap_context with
    | [] -> ()
    | _ ->
      let heap_line = draw_line (line_length - 1) ^ "*" in
      Fmt.pf ppf "%a@,%s@," Fmt.(list ~sep:cut pp_hprop) heap_context heap_line);
    Fmt.pf ppf "  %a@,⊑ %a@," pp_staged_spec l pp_staged_spec r;
    Format.close_box ()
end

module Pstate = struct
  type t = Pctx.t list

  let pp ppf s =
    match s with
    | [] -> Fmt.pf ppf "no more goals"
    | p :: goals1 ->
      let goal_text =
        match List.length goals1 with
        | 0 -> ""
        | n -> Format.asprintf "(%d more goals)" n
      in
      Fmt.pf ppf "@[<v>%a%s@]" Pctx.pp p goal_text
end

module Tactic : sig
  type 'a t

  val run : 'a t -> Pstate.t -> (Pstate.t, string) result
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val map_m : ('a -> 'b t) -> 'a list -> 'b list t
  val iter_m : ('a -> unit t) -> 'a list -> unit t
  val iter_array_m : ('a -> unit t) -> 'a array -> unit t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val fail : string -> 'a t
  val choice : 'a t -> 'a t -> 'a t
  val pop : Pctx.t t
  val push : Pctx.t -> unit t
  val get_rename_ctxt : Bindlib.ctxt t
  val get_goal : sequent t
  val get_lhs : staged_spec t
  val get_rhs : staged_spec t
  val get_constants : term var SMap.t t
  val get_assumptions : prop SMap.t t
  val get_constant : string -> term var t
  val get_assumption : string -> prop t
  val modify_goal : (sequent -> sequent) -> unit t
  val put_rename_ctxt : Bindlib.ctxt -> unit t
  val put_lhs : staged_spec -> unit t
  val put_rhs : staged_spec -> unit t
  val put_goal : staged_spec -> staged_spec -> unit t
  val add_assumption : string -> prop -> unit t
  val add_heap_assumption : hprop -> unit t
  val add_constant : string -> term var -> unit t
  val pop_assumption : string -> prop t (* remove + return *)

  val modify_assumption :
    string -> (prop -> prop t) -> unit t (* this is `modify_m` in Haskell *)
end = struct
  type 'a t = Pstate.t -> ('a * Pstate.t, string) Result.t

  let run t ps = Result.map snd (t ps)
  let fail s = fun _ -> Error s

  let choice t1 t2 =
   fun ps -> match t1 ps with Error _ -> t2 ps | Ok s -> Ok s

  let return x = fun s -> Ok (x, s)
  let bind m f = fun s -> Result.bind (m s) (fun (x, s') -> f x s')
  let ( let* ) = bind

  let rec map_m f xs =
    match xs with
    | [] -> return []
    | x :: xs ->
      let* y = f x in
      let* ys = map_m f xs in
      return (y :: ys)

  let rec iter_m f xs =
    match xs with
    | [] -> return ()
    | x :: xs1 ->
      let* () = f x in
      iter_m f xs1

  let iter_array_m f xs =
    let l = Array.length xs in
    let rec loop i f xs =
      if i < l then
        let* () = f (Array.unsafe_get xs i) in
        loop (i + 1) f xs
      else return ()
    in
    loop 0 f xs

  let get = fun s -> Ok (s, s)
  let put s = fun _ -> Ok ((), s)

  open Pctx

  let get_pctxt =
    let* ps = get in
    match ps with [] -> fail "no more goal" | g :: _ -> return g

  let put_pctxt p =
    let* ps = get in
    match ps with [] -> fail "no more goal" | _ :: ps -> put (p :: ps)

  let modify_pctxt f =
    let* ps = get in
    match ps with [] -> fail "no more goal" | p :: ps -> put (f p :: ps)

  let modify_goal f = modify_pctxt (fun p -> { p with goal = f p.goal })
  let put_goal l r = modify_pctxt (fun p -> { p with goal = (l, r) })
  let put_lhs l = modify_goal (fun (_, r) -> (l, r))
  let put_rhs r = modify_goal (fun (l, _) -> (l, r))

  let put_rename_ctxt rename_ctxt =
    modify_pctxt (fun p -> { p with rename_ctxt })

  let add_constant name t =
    let* pc = get_pctxt in
    if SMap.mem name pc.constants then
      fail ("add_constant: " ^ name ^ " is already used")
    else put_pctxt { pc with constants = SMap.add name t pc.constants }

  let add_assumption name p =
    let* pc = get_pctxt in
    if SMap.mem name pc.assumptions then
      fail ("add_assumption: " ^ name ^ " is already used")
    else put_pctxt { pc with assumptions = SMap.add name p pc.assumptions }

  let pop_assumption name =
    let* pc = get_pctxt in
    match SMap.find_opt name pc.assumptions with
    | None -> fail ("no assumption named: " ^ name)
    | Some p ->
      let assumptions = SMap.remove name pc.assumptions in
      let* _ = put_pctxt { pc with assumptions } in
      return p

  let modify_assumption name f =
    let* p = pop_assumption name in
    let* p = f p in
    add_assumption name p

  let get_rename_ctxt =
    let* p = get_pctxt in
    return p.rename_ctxt

  let get_goal =
    let* p = get_pctxt in
    return p.goal

  let get_lhs =
    let* f1, _ = get_goal in
    return f1

  let get_rhs =
    let* _, f2 = get_goal in
    return f2

  let get_constants =
    let* p = get_pctxt in
    return p.constants

  let get_assumptions =
    let* p = get_pctxt in
    return p.assumptions

  let get_constant x =
    let* constants = get_constants in
    match SMap.find_opt x constants with
    | None -> fail ("no constant named: " ^ x)
    | Some v -> return v

  let get_assumption h =
    let* assumptions = get_assumptions in
    match SMap.find_opt h assumptions with
    | None -> fail ("no assumption named: " ^ h)
    | Some p -> return p

  let pop =
    let* ps = get in
    match ps with
    | [] -> fail "cannot pop goal"
    | g :: gs ->
      let* _ = put gs in
      return g

  let push g =
    let* ps = get in
    put (g :: ps)

  let add_heap_assumption h =
    let* ps = get in
    match ps with
    | [] -> fail "no more goals"
    | g :: gs -> put ({ g with heap_context = h :: g.heap_context } :: gs)
end

let intro_heap =
  let open Tactic in
  let* left = get_lhs in
  match left with
  | Sequence (Ensures h, rest) ->
    let* _ = put_lhs rest in
    add_heap_assumption h
  | _ -> fail "cannot intro lhs"

let intro_pure name =
  let open Tactic in
  let* left = get_lhs in
  match left with
  | Sequence (Ensures (HPure p), rest) ->
    let* _ = put_lhs rest in
    add_assumption name p
  | _ -> fail "cannot intro lhs"

let specialize h ts =
  let open Tactic in
  (* TODO: parse_term with respect to constant context *)
  let ts = List.map parse_term ts |> Array.of_list in
  (* TODO allow not exactly same length? *)
  modify_assumption h (function
    | PForall b -> return (msubst b ts)
    | _ -> fail "not a prop that can be specialised")

let refl =
  let open Tactic in
  let* left, right = get_goal in
  if equal_staged_spec left right then pop
  else fail "cannot close goal using reflexivity"

let forall_intro =
  let open Tactic in
  let* ctxt = get_rename_ctxt in
  let* right = get_rhs in
  match Prenex.move_quantifiers_out right with
  | Forall b ->
    (* TODO freshness issues? this has to be free on both sides *)
    let xs, f, ctxt = unmbind_in ctxt b in
    let* _ = put_rhs f in
    let* _ = put_rename_ctxt ctxt in
    iter_array_m (fun x -> add_constant (name_of x) x) xs
  | _ -> fail "cannot intro forall"

let forall_elim t =
  let open Tactic in
  let* left = get_lhs in
  match Prenex.move_quantifiers_out left with
  | Forall b ->
    (* TODO: parse_term with respect to constant context *)
    let t = List.map parse_term t |> Array.of_list in
    put_lhs (msubst b t)
  | _ -> fail "cannot eliminate forall"

let exists_intro t =
  let open Tactic in
  let* right = get_rhs in
  match Prenex.move_quantifiers_out right with
  | Exists b ->
    (* TODO: parse_term with respect to constant context *)
    let t = List.map parse_term t |> Array.of_list in
    put_rhs (msubst b t)
  | _ -> fail "cannot intro exists"

let exists_elim =
  let open Tactic in
  let* ctxt = get_rename_ctxt in
  let* left = get_lhs in
  match Prenex.move_quantifiers_out left with
  | Exists b ->
    let xs, f, ctxt = unmbind_in ctxt b in
    let* _ = put_lhs f in
    let* _ = put_rename_ctxt ctxt in
    iter_array_m (fun x -> add_constant (name_of x) x) xs
  | _ -> fail "cannot eliminate exists"

let disj_elim =
  let open Tactic in
  let* left, right = get_goal in
  match left with
  | Disjunct (a, b) ->
    let* ps = pop in
    let* _ = push { ps with goal = (a, right) } in
    push { ps with goal = (b, right) }
  | _ -> fail "not a disjunction"

let left =
  let open Tactic in
  let* left, right = get_goal in
  match right with
  | Disjunct (a, _) ->
    let* ps = pop in
    push { ps with goal = (left, a) }
  | _ -> fail "not a disjunction"

let right =
  let open Tactic in
  let* left, right = get_goal in
  match right with
  | Disjunct (_, b) ->
    let* ps = pop in
    push { ps with goal = (left, b) }
  | _ -> fail "not a disjunction"

let simpl =
  let open Tactic in
  let* left, right = get_goal in
  put_goal (Simpl.simpl_staged_spec left) (Simpl.simpl_staged_spec right)

let req_left =
  let open Tactic in
  let* left, right = get_goal in
  match right with
  | Sequence (Requires h, rest) -> put_goal (Sequence (Ensures h, left)) rest
  | Requires h -> put_goal (Sequence (Ensures h, left)) (Ensures HEmp)
  | _ -> fail "cannot do anything"

let solve =
  let open Tactic in
  let* left, right = get_goal in
  let uncons_ens f =
    match f with
    | Sequence (Ensures (HPure p), rest) -> return (p, rest)
    | Ensures (HPure p) -> return (p, Ensures HEmp)
    | _ -> fail "cannot split"
  in
  let* p1, f1 = uncons_ens left in
  let* p2, f2 = uncons_ens right in
  let res = Why3_prover.prove (PImplies (p1, p2)) in
  match res with `Valid -> put_goal f1 f2 | _ -> return ()

(* let induction ~ih wf =
  let open Tactic in
  let* left, right = get_goal in
  (* TODO should be of the form forall n. n < n0 -> ... *)
  add_assumption ih (PImplies (parse_prop wf, PSubsumes (left, right))) *)

module ProofState = struct
  type t = {
    definitions : symbol_table;
    goals : Pstate.t;
  }

  let initial_state = { definitions = empty_table; goals = [] }
  let current_state = ref initial_state
  let reset_proof_state () = current_state := initial_state
  let print_proof_state () = Format.printf "%a@." Pstate.pp !current_state.goals

  (* TODO: add some other command to print definition/hypothesis/etc. *)

  (** Handle definitions *)
  let get_definitions () = !current_state.definitions

  let set_definitions definitions =
    current_state := { !current_state with definitions }

  let set_goals goals = current_state := { !current_state with goals }

  let declare decl =
    let sym, def = open_dfun (parse_decl decl) in
    try
      set_definitions (add_decl sym def !current_state.definitions);
      Format.printf "%s declared@." sym.sym_name
    with Failure msg -> Format.printf "error: %s@." msg

  let start_proof l r =
    set_goals [Pctx.create ~goal:(parse_staged_spec l, parse_staged_spec r) ()];
    print_proof_state ()

  let run_tactic tac =
    match Tactic.run tac !current_state.goals with
    | Ok new_goals ->
      set_goals new_goals;
      print_proof_state ()
    | Error s -> Format.printf "error: %s@." s

  let make_interactive (tac : 'b -> 'a Tactic.t) (arg : 'b) =
    run_tactic (tac arg)

  (* TODO: tactic may need to refer to the global state, not just the current goal itself. *)
end

module Interactive = struct
  open ProofState

  let specialize h = make_interactive (specialize h)
  let refl = make_interactive (fun () -> refl)
  let intro_heap = make_interactive (fun () -> intro_heap)
  let intro_pure = make_interactive intro_pure
  let forall_intro = make_interactive (fun () -> forall_intro)
  let forall_elim = make_interactive forall_elim
  let exists_intro = make_interactive exists_intro
  let exists_elim = make_interactive (fun () -> exists_elim)
  let disj_elim = make_interactive (fun () -> disj_elim)
  let left = make_interactive (fun () -> left)
  let right = make_interactive (fun () -> right)
  let simpl = make_interactive (fun () -> simpl)
  let req_left = make_interactive (fun () -> req_left)
  let solve = make_interactive (fun () -> solve)

  (* let induction ~ih = make_interactive (induction ~ih) *)
  let prove s = Why3_prover.prove (parse_prop s)

  (** Unfold a definition (symbol) on both side of a sequent in the current
      proof state.

      TODO: implement `unfold in`. TODO: report failure using monad. Make it
      consistent *)
  let unfold (sym_name : string) =
    let sym = { sym_name } in
    let definitions = get_definitions () in
    match SymMap.find_opt sym definitions with
    | None -> Format.printf "error: the symbol %s does not exist@." sym_name
    | Some def ->
      let tac =
        let open Tactic in
        let* lhs, rhs = get_goal in
        put_goal (Unfold.unfold sym def lhs) (Unfold.unfold sym def rhs)
      in
      run_tactic tac

  (** Generate an induction hypothesis in the current proof state.

      TODO: add decreasing measurement as a hypothesis for the IH. *)
  let induction (ih : string) (vars : string list) =
    let tac =
      let open Tactic in
      let* assumptions = get_assumptions in
      let* vars = map_m get_constant vars in
      let* lhs, rhs = get_goal in
      let assumptions = List.map snd (SMap.bindings assumptions) in
      let vars = Array.of_list vars in
      (* generate the body of the induction hypothesis *)
      let ih_body = Induction.induction assumptions vars lhs rhs in
      (* and wrap it into a prop *)
      let ih_prop = PForall ih_body in
      add_assumption ih ih_prop
    in
    run_tactic tac

  (* TODO: implement `rewrite in` (but where can we safely rewrite?) *)
  (* TODO: implement rewrite with hypothesis (generate subgoals) *)

  (** Rewrite in the LHS of a sequent. *)
  let rewrite (h : string) =
    let tac =
      let open Tactic in
      let* assumption = get_assumption h in
      let* lhs = get_lhs in
      let rule = Rewrite.prop_to_rule assumption in
      put_lhs (Rewrite.rewrite rule lhs)
    in
    run_tactic tac
end
