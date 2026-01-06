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
  (* Iter.append () (t2 ps) *)

  (* let choices ts = fun ps -> Iter.append_l (List.map (fun t -> t ps) ts) *)

  (* like ltac's lazymatch. unsure if this is necessary as we only get one solution. also this may lead to incompleteness of search, as we cannot backtrack past this, like a cut? *)
  (* let committed_choice (t1 : 'a t) (t2 : 'a t) : 'a t =
   fun ps -> Iter.take 1 ((choice t1 t2) ps) *)

  (* let committed_choices ts = fun ps -> Iter.take 1 ((choices ts) ps) *)

  (* let failure ~title fmt =
    Format.kasprintf
      (fun msg ->
        fun s k ->
         Debug.debug ~at:4 ~title "%s" msg;
         fail s k)
      fmt

  let span (t : 'a t) ~title fmt =
    Format.kasprintf
      (fun msg ->
        fun s k ->
         let@ _ = span (fun _r -> Debug.debug ~at:4 ~title "%s" msg) in
         t s k)
      fmt
*)
end

(* type coq_tactic =
  | Rewrite of string
  | SRReduction
  | Simplify
  | Biab
  | EntDisjL
  | EntDisjR
  | Focus of coq_tactic list

type coq_tactics = coq_tactic list

let rec string_of_coq_tactic t =
  match t with
  | EntDisjL -> "apply ent_disj_l."
  | EntDisjR -> "apply ent_disj_l."
  | Focus [] -> ""
  | Focus [a] -> Format.asprintf "{ %s }" (string_of_coq_tactic a)
  | Focus (a :: rest) ->
    Format.asprintf "{ %s\n%s }" (string_of_coq_tactic a)
      (string_of_list_ind_lines string_of_coq_tactic rest)
  | Simplify -> "fsimpl."
  | Biab -> "fbiabduction."
  | SRReduction -> "freduction."
  | Rewrite r -> Format.asprintf "rewrite %s." r

and string_of_coq_tactics ts =
  ts |> List.map string_of_coq_tactic |> String.concat "\n"

let%expect_test _ =
  Format.printf "%s@."
    (string_of_coq_tactics
       [
         EntDisjL;
         Focus
           [
             EntDisjR;
             EntDisjL;
             EntDisjR;
             EntDisjL;
             EntDisjR;
             EntDisjL;
             EntDisjR;
             EntDisjL;
           ];
         Focus [EntDisjR];
       ]);
  [%expect
    {|
    apply ent_disj_l.
    { apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l.
      apply ent_disj_l. }
    { apply ent_disj_l. }
    |}] *)

let intro =
  let open Tactic in
  let* right = goal_rhs in
  match right with
  | Forall b ->
    let x, f = unbind b in
    (* let* _ = span (with_lhs f1 search) ~title:"disj left" "left branch" in *)
    (* span (with_lhs f2 search) ~title:"disj left" "right branch" *)
    (* with_rhs *)
    (* set *)
    (* let* l = goal_lhs in *)
    (* let* p = ctx in *)
    let* _ = put_rhs f in
    let* pctx = ctx in
    put_pctx { pctx with constants = unbox (Mk.tvar x) :: pctx.constants }
    (* Ok (p, l, f) *)
    (* Ok () *)
    (* return (p, l, f) *)
    (* put  *)
  | _ -> fail "cannot intro"

(* let rec disj_left () : unit Tactic.t =
  let open Tactic in
  let* left = goal_lhs in
  match left with
  | Disjunction (f1, f2) ->
    let* _ = span (with_lhs f1 search) ~title:"disj left" "left branch" in
    span (with_lhs f2 search) ~title:"disj left" "right branch"
  | _ -> fail

and disj_right () : unit Tactic.t =
  let open Tactic in
  let* right = goal_rhs in
  match right with
  | Disjunction (f1, f2) ->
    let goal2 = span (with_rhs f2 search) ~title:"disj right" "right branch" in
    let goal1 = span (with_rhs f1 search) ~title:"disj right" "left branch" in
    choice goal1 goal2
  | _ -> fail

and ens_ens () : unit Tactic.t =
  let open Tactic in
  let* left, right = goal in
  match (left, right) with
  | NormalReturn (True, EmptyHeap), NormalReturn (True, EmptyHeap) ->
    debug ~at:4 ~title:"ens ens" "ok";
    return ()
  | _ -> fail

and search () : unit Tactic.t =
  let open Tactic in
  let* left, right = goal in
  debug ~at:4 ~title:"search" "%s |- %s"
    (string_of_staged_spec left)
    (string_of_staged_spec right);
  choices [disj_left (); disj_right (); ens_ens (); failure ~title:"STUCK" ""]

let%expect_test _ =
  Debug.test_init 4;
  let open Syntax in
  let left = Disjunction (ens (), ens ()) in
  let right = Disjunction (ens ~p:False (), ens ()) in
  let r = Tactic.run (search ()) (new_pctx (), left, right) |> Option.get in
  debug ~at:4 ~title:"done" "%s" (string_of_pstate (r, left, right));
  [%expect
    {|
    * search | _1
    (ens emp) \/ (ens emp) |- (ens F) \/ (ens emp)

    * disj left | _2
    left branch

    ** search | _3
    ens emp |- (ens F) \/ (ens emp)

    ** disj right | _4
    left branch

    *** search | _5
    ens emp |- ens F

    *** STUCK | _6

    *** disj right | _7 <-_4
    left branch

    ** disj right | _8
    right branch

    *** search | _9
    ens emp |- ens emp

    *** ens ens | _10
    ok

    *** disj left | _11
    right branch

    **** search | _12
    ens emp |- (ens F) \/ (ens emp)

    **** disj right | _13
    left branch

    ***** search | _14
    ens emp |- ens F

    ***** STUCK | _15

    ***** disj right | _16 <-_13
    left branch

    **** disj right | _17
    right branch

    ***** search | _18
    ens emp |- ens emp

    ***** ens ens | _19
    ok

    ***** disj right | _20 <-_17
    right branch

    **** disj left | _21 <-_11
    right branch

    *** disj right | _22 <-_8
    right branch

    ** disj left | _23 <-_2
    left branch

    * done | _24
    (ens emp) \/ (ens emp)
    ⊑
    (ens F) \/ (ens emp)
    <============================================================
    constants:
    []

    induction_hypotheses:


    lemmas:


    assumptions:


    definitions_nonrec:


    definitions_rec:


    unfolded:
    |}] *)

module Interactive = struct
  let current_state = ref None

  let print_state () =
    Format.printf "%s@." (show_pstate (Option.get !current_state))

  let start_proof l r =
    current_state :=
      Some (Pctx.create (), parse_staged_spec l, parse_staged_spec r);
    print_state ()

  let apply (tac : 'a Tactic.t) =
    match !current_state with
    | None -> print_endline "No active goal!"
    | Some st ->
      (match tac st with
      | Ok (_, next_st) ->
        current_state := Some next_st;
        (* print_goals next_st *)
        print_state ()
      | Error s ->
        (* print_error e *)
        Format.printf "error applying %s@." s)
end
