open Core.Syntax
open Core.Pretty
open Parsing.Parse
open Bindlib

type goal = staged_spec * staged_spec

module Pctx = struct
  type t = {
    constants : term list;
    (* definitions_nonrec : (string * Rewriting.rule) list; *)
    (* definitions_rec : (string * Rewriting.rule) list; *)
    (* induction_hypotheses : (string * Rewriting.rule) list; *)
    (* lemmas : (string * Rewriting.rule) list; *)
    (* unfolded : use list; *)
    assumptions : prop list;
    goals : (staged_spec * staged_spec) list;
  }

  let create ?(goals = []) () = { constants = []; assumptions = []; goals }
  let draw_line n = String.make n '-'

  let pp ppf { constants; assumptions; goals } =
    match goals with
    | [] -> Fmt.pf ppf "no more goals"
    | (l, r) :: goals1 ->
      let line = draw_line 20 in
      let goal_text =
        match List.length goals1 with
        | 0 -> ""
        | n -> Format.asprintf "(%d more goals)" n
      in
      Fmt.pf ppf "@[<v>@[<hov>%a@]@,%a%s@,  %a@,⊑ %a@,%s@,@]"
        Fmt.(list ~sep:comma pp_term)
        constants
        Fmt.(list ~sep:cut pp_prop)
        assumptions
        (* Format.asprintf "@[<v>@,%a@,@]" Pctx.pp pctx *)
        line pp_staged_spec l pp_staged_spec r goal_text
end

type pstate = Pctx.t

(* let show_pstate (pctx, l, r) = *)

(** Tactics combine the state and list monads *)
module Tactic : sig
  type 'a t = pstate -> ('a * pstate, string) Result.t

  val run : 'a t -> pstate -> Pctx.t option
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val fail : string -> 'a t
  val choice : 'a t -> 'a t -> 'a t
  val get_goal : goal t
  val get_lhs : staged_spec t
  val get_rhs : staged_spec t
  val put_lhs : staged_spec -> unit t
  val put_rhs : staged_spec -> unit t
  val put_goal : staged_spec -> staged_spec -> unit t
  val modify_goal : (goal -> goal) -> unit t
  val add_assumption : prop -> unit t
  val add_constant : term -> unit t

  (* val get_pctx : Pctx.t t



  *)
end = struct
  type 'a t = pstate -> ('a * pstate, string) Result.t

  let run t ps = Result.to_option (t ps) |> Option.map snd
  let fail s = fun _ -> Error s

  let choice t1 t2 =
   fun ps -> match t1 ps with Error _ -> t2 ps | Ok s -> Ok s

  let return x = fun s -> Ok (x, s)
  let bind m f = fun s -> Result.bind (m s) (fun (x, s') -> f x s')
  let ( let* ) = bind
  let get = fun s -> Ok (s, s)

  (* let get_pctx =
    let* r, _, _ = get in
    return r *)

  open Pctx

  let get_goal =
    let* pctx = get in
    match pctx.goals with
    | [] -> fail "no more goals"
    | (f1, f2) :: _ -> return (f1, f2)

  let get_lhs =
    let* f1, _ = get_goal in
    return f1

  let get_rhs =
    let* _, f2 = get_goal in
    return f2

  let put s = fun _ -> Ok ((), s)

  (* let put_pctx pctx =
    let* _, f1, f2 = get in
    put (pctx, f1, f2) *)

  let modify_goal f =
    let* pctx = get in
    match pctx.goals with
    | [] -> fail "no more goals"
    | g :: gs -> put { pctx with goals = f g :: gs }

  let put_goal l r = modify_goal (fun _ -> (l, r))
  let put_lhs l = modify_goal (fun (_, r) -> (l, r))
  let put_rhs r = modify_goal (fun (l, _) -> (l, r))

  let add_assumption p =
    let* pctx = get in
    put Pctx.{ pctx with assumptions = p :: pctx.assumptions }

  let add_constant t =
    let* pctx = get in
    put Pctx.{ pctx with constants = t :: pctx.constants }
end

let intro =
  let open Tactic in
  let* right = get_rhs in
  match right with
  | Forall b ->
    (* TODO freshness issues? this has to be free on both sides *)
    let x, f = unbind b in
    let* _ = put_rhs f in
    add_constant (unbox (Mk.tvar x))
  | _ -> fail "cannot intro"

let simpl =
  let open Tactic in
  let* left, right = get_goal in
  put_goal (Simpl.simpl_staged_spec left) (Simpl.simpl_staged_spec right)

let induction wf =
  let open Tactic in
  let* left, right = get_goal in
  (* TODO should be of the form forall n. n < n0 -> ... *)
  add_assumption (PImplies (parse_prop wf, PSubsumes (left, right)))

module ProofState = struct
  let current_state = ref None

  let print_proof_state () =
    Format.printf "%a@." Pctx.pp (Option.get !current_state)

  let start_proof l r =
    current_state :=
      Some (Pctx.create ~goals:[(parse_staged_spec l, parse_staged_spec r)] ());
    print_proof_state ()

  let make_interactive (tac : 'b -> 'a Tactic.t) (arg : 'b) =
    match !current_state with
    | None -> Format.printf "no goal@."
    | Some st ->
      (match tac arg st with
      | Ok (_, next_st) ->
        current_state := Some next_st;
        print_proof_state ()
      | Error s -> Format.printf "error: %s@." s)
end

module Interactive = struct
  open ProofState

  let intro = make_interactive (fun () -> intro)
  let simpl = make_interactive (fun () -> simpl)
  let induction = make_interactive induction
  let smt () = Why3_prover.prove (PAtom TTrue) (PAtom TTrue)
  let prove s = Why3_prover.prove (PAtom TTrue) (parse_prop s)
end
