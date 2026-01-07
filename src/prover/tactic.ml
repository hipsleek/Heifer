open Core.Syntax
open Core.Pretty
open Parsing.Parse
open Bindlib

module Pctx = struct
  type t = {
    constants : term list;
    (* definitions_nonrec : (string * Rewriting.rule) list; *)
    (* definitions_rec : (string * Rewriting.rule) list; *)
    (* induction_hypotheses : (string * Rewriting.rule) list; *)
    (* lemmas : (string * Rewriting.rule) list; *)
    (* unfolded : use list; *)
    assumptions : prop list;
  }

  let create () = { constants = []; assumptions = [] }

  let pp ppf { constants; assumptions } =
    Fmt.pf ppf "@[<v>constants: @[<hov>%a@]@,assumptions: @[<hov>%a@]@]"
      Fmt.(list ~sep:semi pp_term)
      constants
      Fmt.(list ~sep:semi pp_prop)
      assumptions
end

type pstate = Pctx.t * staged_spec * staged_spec

let show_pstate (pctx, l, r) =
  let draw_line n = String.make n '-' in
  let line = draw_line 20 in
  Format.asprintf "@[<v>@,%a@,%s@,  %a@,⊑ %a@,@]" Pctx.pp pctx line
    pp_staged_spec l pp_staged_spec r

(** Tactics combine the state and list monads *)
module Tactic : sig
  type 'a t = pstate -> ('a * pstate, string) Result.t

  val run : 'a t -> pstate -> Pctx.t option
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ctx : Pctx.t t

  type goal = staged_spec * staged_spec

  val goal : goal t
  val goal_lhs : staged_spec t
  val goal_rhs : staged_spec t
  val with_lhs : staged_spec -> (unit -> 'a t) -> 'a t
  val with_rhs : staged_spec -> (unit -> 'a t) -> 'a t
  val fail : string -> 'a t
  val choice : 'a t -> 'a t -> 'a t
  val put_lhs : staged_spec -> unit t
  val put_rhs : staged_spec -> unit t
  val put_pctx : Pctx.t -> unit t

  (*
  val choices : 'a t list -> 'a t
  val committed_choice : 'a t -> 'a t -> 'a t
  val committed_choices : 'a t list -> 'a t *)

  (* val failure :
    title:string -> ('a, Format.formatter, unit, unit t) format4 -> 'a

  val span :
    'a t -> title:string -> ('b, Format.formatter, unit, 'a t) format4 -> 'b *)
end = struct
  (* [@@@warning "-unused-value-declaration"] *)

  type 'a t = pstate -> ('a * pstate, string) Result.t
  type goal = staged_spec * staged_spec

  let run t ps =
    Result.to_option (t ps) |> Option.map (fun (_, (pctx, _, _)) -> pctx)

  let fail s = fun _ -> Error s
  let return x = fun s -> Ok (x, s)
  let bind m f = fun s -> Result.bind (m s) (fun (x, s') -> f x s')
  let ( let* ) = bind
  let get = fun s -> Ok (s, s)

  let ctx =
    let* r, _, _ = get in
    return r

  let goal =
    let* _, f1, f2 = get in
    return (f1, f2)

  let goal_lhs =
    let* _, f1, _ = get in
    return f1

  let goal_rhs =
    let* _, _, f2 = get in
    return f2

  let put s = fun _ -> Ok ((), s)

  let put_pctx pctx =
    let* _, f1, f2 = get in
    put (pctx, f1, f2)

  let put_lhs f1 =
    let* pctx, _, f2 = get in
    put (pctx, f1, f2)

  let put_rhs f2 =
    let* pctx, f1, _ = get in
    put (pctx, f1, f2)

  let put_goal (f1, f2) =
    let* pctx, _, _ = get in
    put (pctx, f1, f2)

  (* let with_ (pctx, f1, f2) t =
    let* _ = put (pctx, f1, f2) in
    t () *)

  let with_lhs f1 t =
    let* of1, of2 = goal in
    let* () = put_lhs f1 in
    let* r = t () in
    let* () = put_goal (of1, of2) in
    return r

  let with_rhs f2 t =
    let* of1, of2 = goal in
    let* () = put_rhs f2 in
    let* r = t () in
    let* () = put_goal (of1, of2) in
    return r

  let choice t1 t2 =
   fun ps -> match t1 ps with Error _ -> t2 ps | Ok s -> Ok s
end

let intro =
  let open Tactic in
  let* right = goal_rhs in
  match right with
  | Forall b ->
    (* TODO freshness issues? this has to be free on both sides *)
    let x, f = unbind b in
    let* _ = put_rhs f in
    let* pctx = ctx in
    put_pctx { pctx with constants = unbox (Mk.tvar x) :: pctx.constants }
  | _ -> fail "cannot intro"

let simpl =
  let open Tactic in
  let* left = goal_lhs in
  let* right = goal_rhs in
  let* _ = put_lhs (Simpl.simpl_staged_spec left) in
  put_rhs (Simpl.simpl_staged_spec right)

module Interactive = struct
  let current_state = ref None

  let print_proof_state () =
    Format.printf "%s@." (show_pstate (Option.get !current_state))

  let start_proof l r =
    current_state :=
      Some (Pctx.create (), parse_staged_spec l, parse_staged_spec r);
    print_proof_state ()

  let make_interactive (tac : 'a Tactic.t) () =
    match !current_state with
    | None -> Format.printf "no goal@."
    | Some st ->
      (match tac st with
      | Ok (_, next_st) ->
        current_state := Some next_st;
        print_proof_state ()
      | Error s -> Format.printf "error: %s@." s)

  let intro = make_interactive intro
  let simpl = make_interactive simpl
end
