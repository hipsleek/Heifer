open Core
open Core.Syntax
open Core.Pretty
open Util.Strings
open Tactic
open Tactics

let fresh =
  let* ctxt = get_rename_ctxt in
  let name, ctxt = Rename.Core.new_name "H" ctxt in
  let* () = put_rename_ctxt ctxt in
  pure name

let rec repeat (tac : unit t) : unit t =
 fun s ->
  match tac s with
  | Error _ ->
      (* Format.printf "repeat stopped@."; *)
      (* repeat never fails *)
      (* TODO repeat should stop when progress stops, not on failure? *)
      Ok ((), s)
  | Ok ((), s1) ->
      (* Format.printf "repeating@."; *)
      repeat tac s1

(* TODO solve or not at all? *)
(* this is parsec try, not ltac try *)
let try_ tac =
 fun s ->
  match tac s with
  | Error _ ->
      (* Error m *)
      Ok ((), s)
  | Ok ((), s1) -> Ok ((), s1)

let maybe_prove_pure =
  let* g = get_goal in
  (* Format.printf "maybe prove pure %a@." pp_term g; *)
  match g with
  | Subsumes _ ->
      (* TODO check for pure *)
      prove
  | Apply (_, _) ->
      (* TODO f is free *)
      prove
  | _ -> failf "doesn't look like a pure thing"

let intro_pure =
  let* n = fresh in
  Pure.intro_pure n

let dbg s = printf "%s" s

let ( >> ) a b =
  let* () = a in
  b

let ( >>> ) a b =
  let* r = a in
  let* () = b in
  pure r

(* let with_focus tac f =
    let* gs = get in
    match gs with
    | [] -> failf "no goals to solve"
    | g :: _gs ->
        let* () = put [g] in
        let* () = tac in
        let* gs1 = get in
        f gs1
  (* (match gs1 with
        | [] -> put gs
        | _ -> failf "failed to solve entirely") *) *)

(* core automation tactic *)
type cert_tac =
  | Smt of term
  | Forall_intro
  | Exists_elim
  | Intro_pure
  | Rewrite of term * cert list * cert
  | Disj_elim of cert * cert

and cert = cert_tac list

let rec pp_cert_tac ppf =
  let spaced_parens pp ppf v = Fmt.pf ppf "@[<1>( %a )@]" pp v in
  function
  | Smt t -> Fmt.pf ppf "prove () (* %a *)" pp_term t
  | Forall_intro -> Fmt.string ppf "forall_intro ()"
  | Exists_elim -> Fmt.string ppf "exists_elim ()"
  | Intro_pure -> Fmt.string ppf "intro_pure \"_\""
  | Rewrite (t, c, k) ->
      (* TODO make this proof script executable, with names, etc. *)
      Fmt.pf ppf "@[<v>rewrite \"_\" (* %a *);" pp_term t;
      (match c with
      | [] -> ()
      | [_] -> Fmt.pf ppf "@ %a" (Fmt.(list ~sep:(any ";@ ")) (spaced_parens pp_cert)) c
      | _ -> Fmt.pf ppf "@,%a" (Fmt.(list ~sep:(any ";@,")) (spaced_parens pp_cert)) c);
      Fmt.pf ppf "@,%a@]" pp_cert k
  | Disj_elim (c1, c2) ->
      Fmt.pf ppf "@[<v>disj_elim ();@,( @[<v 2>%a@] )@,( @[<v 2>%a )@]@]" pp_cert c1 pp_cert c2

and pp_cert ppf c = Fmt.pf ppf "@[<v>%a@]" Fmt.(list ~sep:(any ";@,") pp_cert_tac) c

let focus_and_solve_with tac =
  let* gs = get in
  match gs with
  | [] -> failf "no goals to solve"
  | g :: gs ->
      let* () = put [g] in
      let* r = tac in
      let* gs1 = get in
      (match gs1 with
      | [] ->
          let* () = put gs in
          pure r
      | _ ->
          Format.printf "%a@." Pstate.pp gs1;
          failf "failed to solve entirely")

let focus =
  let* gs = get in
  match gs with
  | [] -> failf "no goals to solve"
  | g :: gs ->
      let* () = put [g] in
      pure gs

(* let* () = tac in
        let* gs1 = get in
        (match gs1 with
        | [] -> put gs
        | _ -> failf "failed to solve entirely") *)

(* let focus_on g =
    let* gs = get in
    match gs with
    | [] -> failf "no goals to solve"
    | _ :: _ ->
        let* () = put [g] in
        pure gs *)

let rec init xs =
  match xs with
  | [] -> failwith "empty"
  | [x] -> ([], x)
  | x :: xs1 ->
      let xs1, y = init xs1 in
      (x :: xs1, y)

let possible_rewrites2 self : cert_tac t list t =
  (* TODO prevent a rewrite from being taken multiple times *)
  let* hyps = get_assumptions <&> SMap.bindings in
  pure
    (hyps
    |> List.filter_map (fun (_, s) ->
        match s with
        | Forall _ | Implies _ | Subsumes _ | Binop (Eq, _, _) ->
            (* TODO use rewrite parsing function *)
            (* TODO take lemmas from global context? *)
            (* Format.printf "chosen for rewrite %a@." pp_term s; *)
            Some
              (let* () = rewrite `Ltr s in
               (* Format.printf "rewrote %a@." pp_term s; *)
               let* gs = get in
               let* sub : cert list =
                 map_m
                   (fun g ->
                     let* () = put [g] in
                     self ())
                   gs
               in
               let* () = put [] in
               let init, tail = init sub in
               pure (Rewrite (s, init, tail)))
        | _ -> None))

let disj_elim self =
  (* TODO may be able to factor out *)
  (* let* rest = focus in *)
  let* () = Disj.disj_elim in
  (* Format.printf "disj elim succeeded@."; *)
  let* gs = get in
  match gs with
  | l :: r :: rest ->
      let* () = put [l] in
      let* pl = self () in
      let* () = put [r] in
      let* pr = self () in
      let* () = put rest in
      (* let* () = put rest in *)
      pure (Disj_elim (pl, pr))
  | _ ->
      Format.printf "failed@.";
      failf "invalid state after disj, tactic error?"

let solve_cert : cert t =
  (* let* gs = get in *)
  (* with_focus Disj.disj_elim (fun gs1 -> pure ()) *)
  let rec solve () : cert t =
    let* g = get in
    (* Format.printf "solving %a@." Pstate.pp g; *)
    (* Format.printf "---@."; *)
    (* let _ : cert t list = possible_rewrites in *)
    match g with
    | [] ->
        (* Format.printf "return empty@."; *)
        pure []
    | _ :: _ ->
        let* possible_rewrites = possible_rewrites2 solve in
        (* catch *)
        let* pf =
          Simpl.simpl
          >> choices
               ([
                  (* debug "about to disj_elim" @@ *)
                  disj_elim solve (* >>> dbg "disj" *);
                  (* debug "about to forall_intro" @@ *)
                  forall_intro >> pure Forall_intro (* >>> dbg "forall intro" *);
                  (* debug "about to exists_elim" @@ *)
                  exists_elim >> pure Exists_elim (* >>> dbg "exists elim" *);
                  (* debug "about to intro_pure"@@ *)
                  intro_pure >> pure Intro_pure (* >>> dbg "intro pure" *);
                ]
               @ possible_rewrites
               @ [
                   (* debug "about to prove" @@ *)
                   get_goal <&> (fun g -> Smt g) >>> maybe_prove_pure (* >>> dbg "smt"; *);
                 ])
        in
        (* Format.printf "pf %a@." pp_cert_tac pf; *)
        let* r = solve () in
        (* Format.printf "solve returned %a@." pp_cert r; *)
        (* Format.printf "result is %a@." pp_cert (pf :: r); *)
        pure (pf :: r)
  in
  let* r = focus_and_solve_with (solve ()) in
  (* Format.printf "result %a@." pp_cert r; *)
  pure r

let possible_rewrites : unit t list t =
  let* hyps = get_assumptions <&> SMap.bindings in
  pure
    (hyps
    |> List.filter_map (fun (_, s) ->
        match s with
        | Forall _ | Implies _ | Subsumes _ | Binop (Eq, _, _) ->
            (* TODO use rewrite parsing function *)
            (* TODO take lemmas from global context? *)
            (* Format.printf "chosen for rewrite %a@." pp_term s; *)
            Some (rewrite `Ltr s)
        | _ -> None))

(* try to solve the current goal and any subgoals it generates *)
let simple =
  let try_to_solve =
    (* TODO certificate generation *)
    let* possible_rewrites = possible_rewrites in
    repeat
      (Simpl.simpl
      >> choices
           ([
              Disj.disj_elim >> dbg "disj";
              forall_intro >> dbg "forall";
              exists_elim >> dbg "exists";
              intro_pure >> dbg "intro pure";
            ]
           @ [maybe_prove_pure >> dbg "prove pure"]
           @ possible_rewrites))
  in
  try_ (focus_and_solve_with try_to_solve)
