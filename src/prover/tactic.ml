open Core.Syntax
open Core.Pretty
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
    Fmt.(list ~sep:(any ",@ ") (pair ~sep:(any ":@ ") pp_k pp_v))
    al

type sequent = staged_spec * staged_spec

module Pctx = struct
  type t = {
    constants : term list;
    assumptions : prop SMap.t;
    goal : sequent;
  }

  let create ~goal () = { constants = []; assumptions = SMap.empty; goal }
  let draw_line n = String.make n '-'

  let pp ppf { constants; assumptions; goal = l, r } =
    let line = draw_line 20 in
    Fmt.pf ppf "@[<v>@[<hov>%a@]@,%a%s@,  %a@,⊑ %a@,@]"
      Fmt.(list ~sep:comma pp_term)
      constants
      (pp_hypotheses ~pp_k:Fmt.string ~pp_v:pp_prop)
      assumptions line pp_staged_spec l pp_staged_spec r
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
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val fail : string -> 'a t
  val choice : 'a t -> 'a t -> 'a t
  val pop_goal : Pctx.t t
  val push_goal : Pctx.t -> unit t
  val get_goal : sequent t
  val get_lhs : staged_spec t
  val get_rhs : staged_spec t
  val modify_goal : (sequent -> sequent) -> unit t
  val put_lhs : staged_spec -> unit t
  val put_rhs : staged_spec -> unit t
  val put_goal : staged_spec -> staged_spec -> unit t
  val add_assumption : string -> prop -> unit t
  val add_constant : term -> unit t
end = struct
  type 'a t = Pstate.t -> ('a * Pstate.t, string) Result.t

  let run t ps = Result.map snd (t ps)
  let fail s = fun _ -> Error s

  let choice t1 t2 =
   fun ps -> match t1 ps with Error _ -> t2 ps | Ok s -> Ok s

  let return x = fun s -> Ok (x, s)
  let bind m f = fun s -> Result.bind (m s) (fun (x, s') -> f x s')
  let ( let* ) = bind
  let get = fun s -> Ok (s, s)

  open Pctx

  let get_goal =
    let* ps = get in
    match ps with [] -> fail "no more goals" | g :: _ -> return g.goal

  let get_lhs =
    let* f1, _ = get_goal in
    return f1

  let get_rhs =
    let* _, f2 = get_goal in
    return f2

  let put s = fun _ -> Ok ((), s)

  let modify_goal f =
    let* ps = get in
    match ps with
    | [] -> fail "no more goals"
    | g :: gs -> put ({ g with goal = f g.goal } :: gs)

  let pop_goal =
    let* ps = get in
    match ps with
    | [] -> fail "cannot pop goal"
    | g :: gs ->
      let* _ = put gs in
      return g

  let push_goal g =
    let* ps = get in
    put (g :: ps)

  let put_goal l r = modify_goal (fun _ -> (l, r))
  let put_lhs l = modify_goal (fun (_, r) -> (l, r))
  let put_rhs r = modify_goal (fun (l, _) -> (l, r))

  let add_assumption name pr =
    let* ps = get in
    match ps with
    | [] -> fail "no more goals"
    | g :: gs ->
      put ({ g with assumptions = SMap.add name pr g.assumptions } :: gs)

  let add_constant t =
    let* ps = get in
    match ps with
    | [] -> fail "no more goals"
    | g :: gs -> put ({ g with constants = t :: g.constants } :: gs)
end

let refl =
  let open Tactic in
  let* left, right = get_goal in
  if equal_staged_spec left right then pop_goal
  else fail "cannot close goal using reflexivity"

let forall_intro =
  let open Tactic in
  let* right = get_rhs in
  match right with
  | Forall b ->
    (* TODO freshness issues? this has to be free on both sides *)
    let x, f = unbind b in
    let* _ = put_rhs f in
    add_constant (unbox (Mk.tvar x))
  | _ -> fail "cannot intro"

let disj_elim =
  let open Tactic in
  let* left, right = get_goal in
  match left with
  | Disjunct (a, b) ->
    let* ps = pop_goal in
    let* _ = push_goal { ps with goal = (a, right) } in
    push_goal { ps with goal = (b, right) }
  | _ -> fail "not a disjunction"

let left =
  let open Tactic in
  let* left, right = get_goal in
  match right with
  | Disjunct (a, _) ->
    let* ps = pop_goal in
    push_goal { ps with goal = (left, a) }
  | _ -> fail "not a disjunction"

let right =
  let open Tactic in
  let* left, right = get_goal in
  match right with
  | Disjunct (_, b) ->
    let* ps = pop_goal in
    push_goal { ps with goal = (left, b) }
  | _ -> fail "not a disjunction"

let simpl =
  let open Tactic in
  let* left, right = get_goal in
  put_goal (Simpl.simpl_staged_spec left) (Simpl.simpl_staged_spec right)

let induction ~ih wf =
  let open Tactic in
  let* left, right = get_goal in
  (* TODO should be of the form forall n. n < n0 -> ... *)
  add_assumption ih (PImplies (parse_prop wf, PSubsumes (left, right)))

module ProofState = struct
  let current_state = ref []
  let print_proof_state () = Format.printf "%a@." Pstate.pp !current_state

  let start_proof l r =
    current_state :=
      [Pctx.create ~goal:(parse_staged_spec l, parse_staged_spec r) ()];
    print_proof_state ()

  let make_interactive (tac : 'b -> 'a Tactic.t) (arg : 'b) =
    match Tactic.run (tac arg) !current_state with
    | Ok next_st ->
      current_state := next_st;
      print_proof_state ()
    | Error s -> Format.printf "error: %s@." s
end

module Interactive = struct
  open ProofState

  let refl = make_interactive (fun () -> refl)
  let forall_intro = make_interactive (fun () -> forall_intro)
  let disj_elim = make_interactive (fun () -> disj_elim)
  let left = make_interactive (fun () -> left)
  let right = make_interactive (fun () -> right)
  let simpl = make_interactive (fun () -> simpl)
  let induction ~ih = make_interactive (induction ~ih)
  let smt () = Why3_prover.prove (PAtom TTrue) (PAtom TTrue)
  let prove s = Why3_prover.prove (PAtom TTrue) (parse_prop s)
end
