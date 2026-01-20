open Core
open Util
open Core.Syntax
open Core.Pretty
open Core.Decl
open Core.Syntax_util
open Bindlib
open Util.Strings

module Options = struct
  let show_why3_goal = ref false
end

(* TODO: refactor to proof_state.ml. proof_state will depend on proof_context *)
module Pstate = struct
  open Proof_context

  type t = proof_context list

  let destruct = List.map Lists.singleton

  let focus = function
    | [] -> ([], [])
    | s :: ss -> ([s], ss)

  let append = List.append

  let pp ppf s =
    match s with
    | [] -> Fmt.pf ppf "no more goals"
    | g :: gs ->
        Fmt.pf ppf "@[<v>@,%a" pp_proof_context g;
        (match List.length gs with
        | 0 -> ()
        | n -> Fmt.pf ppf "@,(%d more goals)" n);
        Fmt.pf ppf "@,@]"
end

(* TODO: refactor to tactic_monad.ml. tactic_monad will depend on proof_state. *)
module Tactic : sig
  open Proof_context

  type 'a t = Pstate.t -> ('a * Pstate.t, string) Result.t

  val run : 'a t -> Pstate.t -> (Pstate.t, string) result

  (* basic combinators *)
  val pure : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val mapl : 'b -> 'a t -> 'b t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t
  val ( <&> ) : 'a t -> ('a -> 'b) -> 'b t
  val ( <$ ) : 'b -> 'a t -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val fail : string -> 'a t
  val failf : ('a, Format.formatter, unit, 'b t) format4 -> 'a
  val try_ : 'a t -> ('a, string) result t
  val catch : 'a t -> (string -> 'a t) -> 'a t
  val choice : 'a t -> 'a t -> 'a t
  val choices : ?err:string -> 'a t list -> 'a t
  val get : Pstate.t t
  val put : Pstate.t -> unit t
  val gets : (Pstate.t -> 'a) -> 'a t
  val modify : (Pstate.t -> Pstate.t) -> unit t

  (* higher-order combinators, with other datatypes *)
  val map_m : ('a -> 'b t) -> 'a list -> 'b list t
  val iter_m : ('a -> unit t) -> 'a list -> unit t
  val iter_array_m : ('a -> unit t) -> 'a array -> unit t

  (* derived combinators: managing pctxts *)
  val pop_pctxt : proof_context t
  val push_pctxt : proof_context -> unit t
  val get_pctxt : proof_context t
  val put_pctxt : proof_context -> unit t
  val gets_pctxt : (proof_context -> 'a) -> 'a t
  val modify_pctxt : (proof_context -> proof_context) -> unit t

  (* derived combinators: get *)
  val get_rename_ctxt : Bindlib.ctxt t
  val get_constants : term var SMap.t t
  val get_assumptions : term SMap.t t
  val get_heap_assumptions : term list t
  val get_goal : term t
  val get_constant : string -> term var t
  val get_assumption : string -> term t

  (* val get_heap_assumption : string -> term t *)
  (* derived combinators: put *)
  val put_rename_ctxt : Bindlib.ctxt -> unit t
  val put_constants : term var SMap.t -> unit t
  val put_assumptions : term SMap.t -> unit t
  val put_heap_assumptions : term list -> unit t
  val put_goal : term -> unit t
  val add_constant : string -> term var -> unit t
  val add_assumption : string -> term -> unit t

  (* val add_heap_assumption : string -> term -> unit t *)
  (* derived combinators: modify *)
  val pop_assumption : string -> term t (* remove + return *)

  (* val pop_heap_assumption : string -> term t *)
  val modify_goal : (term -> term) -> unit t
  val modify_heap_assumptions : (term list -> term list) -> unit t
end = struct
  open Proof_context

  type 'a t = Pstate.t -> ('a * Pstate.t, string) Result.t

  let run m s = Result.map snd (m s)
  let fail s = fun _ -> Error s
  let failf fmt = Format.kasprintf fail fmt
  let pure x = fun s -> Ok (x, s)
  let map f m = fun s -> Result.map (fun (x, s) -> (f x, s)) (m s)
  let mapl x m = fun s -> Result.map (fun (_, s) -> (x, s)) (m s)
  let bind m f = fun s -> Result.bind (m s) (fun (x, s) -> f x s)
  let ( <$> ) = map
  let ( <$ ) = mapl
  let ( <&> ) m f = map f m
  let ( >>= ) = bind
  let ( let+ ) m f = map f m
  let ( let* ) = bind

  let choice m1 m2 =
   fun s ->
    let r = m1 s in
    match r with
    | Ok _ -> r
    | Error _ -> m2 s

  let rec choices ?(err = "empty choice") ms =
   fun s ->
    match ms with
    | [] -> Error err
    | m :: ms ->
        let r = m s in
        (match r with
        | Ok _ -> r
        (* TODO possibly use a list or tree of errors *)
        | Error e ->
            Result.map_error (Format.asprintf "%s / %s" e) (choices ~err ms s))

  let rec map_m f = function
    | [] -> pure []
    | x :: xs ->
        let* y = f x in
        let* ys = map_m f xs in
        pure (y :: ys)

  let rec iter_m f = function
    | [] -> pure ()
    | x :: xs ->
        let* _ = f x in
        iter_m f xs

  let iter_array_m f xs =
    let l = Array.length xs in
    let rec loop i =
      if i < l then
        let* _ = f (Array.unsafe_get xs i) in
        loop (i + 1)
      else pure ()
    in
    loop 0

  let catch m h =
   fun s ->
    let r = m s in
    match r with
    | Ok _ -> r
    | Error e -> h e s

  let try_ m =
   fun s ->
    match m s with
    | Ok (x, s) -> Ok (Ok x, s)
    | Error e -> Ok (Error e, s)

  let get = fun s -> Ok (s, s)
  let put s = fun _ -> Ok ((), s)
  let gets f = fun s -> Ok (f s, s)
  let modify f = fun s -> Ok ((), f s)

  let pop_pctxt =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | p :: ps ->
        let+ _ = put ps in
        p

  let push_pctxt p = modify (fun ps -> p :: ps)

  let get_pctxt =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | p :: _ -> pure p

  let put_pctxt p =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | _ :: ps -> put (p :: ps)

  let gets_pctxt f =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | p :: _ -> pure (f p)

  let modify_pctxt f =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | p :: ps -> put (f p :: ps)

  let get_rename_ctxt = gets_pctxt (fun p -> p.rename_ctxt)
  let get_constants = gets_pctxt (fun p -> p.constants)
  let get_assumptions = gets_pctxt (fun p -> p.assumptions)
  let get_heap_assumptions = gets_pctxt (fun p -> p.heap_assumptions)
  let get_goal = gets_pctxt (fun p -> p.goal)

  let get_constant name =
    let* constants = get_constants in
    match SMap.find_opt name constants with
    | None -> fail ("no constant named: " ^ name)
    | Some v -> pure v

  let get_assumption name =
    let* assumptions = get_assumptions in
    match SMap.find_opt name assumptions with
    | None -> fail ("no assumption named: " ^ name)
    | Some t -> pure t

  (* let get_heap_assumption name =
    let* heap_assumptions = get_heap_assumptions in
    match SMap.find_opt name heap_assumptions with
    | None -> fail ("no heap assumption named: " ^ name)
    | Some t -> return t *)

  let put_rename_ctxt rename_ctxt =
    modify_pctxt (fun p -> { p with rename_ctxt })

  let put_constants constants = modify_pctxt (fun p -> { p with constants })

  let put_assumptions assumptions =
    modify_pctxt (fun p -> { p with assumptions })

  let put_heap_assumptions heap_assumptions =
    modify_pctxt (fun p -> { p with heap_assumptions })

  let put_goal goal = modify_pctxt (fun p -> { p with goal })

  let add_constant name v =
    let* constants = get_constants in
    if SMap.mem name constants then
      fail ("add_constant: " ^ name ^ " is already used")
    else put_constants (SMap.add name v constants)

  let add_assumption name t =
    let* assumptions = get_assumptions in
    if SMap.mem name assumptions then
      fail ("add_assumption: " ^ name ^ " is already used")
    else put_assumptions (SMap.add name t assumptions)

  (* let add_heap_assumption name t =
    let* heap_assumptions = get_heap_assumptions in
    if SMap.mem name heap_assumptions
    then fail ("add_heap_assumption: " ^ name ^ " is already used")
    else put_heap_assumptions (SMap.add name t heap_assumptions) *)

  let pop_assumption name =
    let* assumptions = get_assumptions in
    match SMap.find_opt name assumptions with
    | None -> fail ("no assumption named: " ^ name)
    | Some t ->
        let+ _ = put_assumptions (SMap.remove name assumptions) in
        t

  (* let pop_heap_assumption name =
    let* heap_assumptions = get_heap_assumptions in
    match SMap.find_opt name heap_assumptions with
    | None -> fail ("no heap assumption named: " ^ name)
    | Some t ->
        let+ _ = put_heap_assumptions (SMap.remove name heap_assumptions) in
        t *)

  let modify_goal f = modify_pctxt (fun p -> { p with goal = f p.goal })

  let modify_heap_assumptions f =
    modify_pctxt (fun p -> { p with heap_assumptions = f p.heap_assumptions })
end

let is_pure t =
  match t with
  | Emp | PointsTo _ | SepConj _ -> false
  | _ -> true

let is_heap t =
  match t with
  | Emp | PointsTo _ | SepConj _ -> true
  | _ -> false

let admit =
  let open Tactic in
  () <$ pop_pctxt

let dup =
  let open Tactic in
  let* p = pop_pctxt in
  let* _ = push_pctxt p in
  push_pctxt p

let uncons_ens f =
  let open Tactic in
  match f with
  | Sequence (Ensures p, rest) when is_pure p -> pure (p, rest)
  | Ensures p when is_pure p -> pure (p, Ensures Emp)
  | _ -> fail "cannot uncons pure ens"

let uncons_req f =
  let open Tactic in
  match f with
  | Sequence (Requires p, rest) when is_pure p -> pure (p, rest)
  | Requires p when is_pure p -> pure (p, Requires Emp)
  | _ -> fail "cannot uncons pure req"

let get_subsumption =
  let open Tactic in
  let* t = get_goal in
  match t with
  | Subsumes (lhs, rhs) -> pure (lhs, rhs)
  | _ -> fail (Format.asprintf "get_subsumption: %a" pp_term t)

let put_subsumption lhs rhs =
  let open Tactic in
  put_goal (Subsumes (lhs, rhs))

let put_lhs lhs =
  let open Tactic in
  let* _, rhs = get_subsumption in
  put_subsumption lhs rhs

let put_rhs rhs =
  let open Tactic in
  let* lhs, _ = get_subsumption in
  put_subsumption lhs rhs

let get_lhs =
  let open Tactic in
  let+ lhs, _ = get_subsumption in
  lhs

let get_rhs =
  let open Tactic in
  let+ _, rhs = get_subsumption in
  rhs

let unwrap o e =
  let open Tactic in
  match o with
  | None -> fail e
  | Some x -> pure x

let guard b e =
  let open Tactic in
  if b then pure () else fail e

let all_goals tac =
 fun s ->
  let open Results.Monad in
  let rec loop = function
    | [] -> pure []
    | s :: ss ->
        let* s1 = Tactic.run tac s in
        let+ s2 = loop ss in
        Pstate.append s1 s2
  in
  let+ s = loop (Pstate.destruct s) in
  ((), s)

let semicolon1 tac1 tac2 =
  let open Tactic in
  let* _ = tac1 in
  all_goals tac2

let semicolon tac1 tac2 =
 fun s ->
  let open Results.Monad in
  let s1, s2 = Pstate.focus s in
  let+ s1 = Tactic.run (semicolon1 tac1 tac2) s1 in
  Pstate.append s1 s2

let invoke_why3 goal =
  let open Tactic in
  let* constants = get_constants in
  let+ assumptions = get_assumptions in
  let constants =
    Array.of_list (SMap.fold (fun _ c acc -> c :: acc) constants [])
  in
  let handle_assumption _ assumption goal =
    if Why3_prover.is_translatable assumption then Implies (assumption, goal)
    else goal
  in
  let why3_goal = SMap.fold handle_assumption assumptions goal in
  let why3_goal =
    unbox (Mk.forall (bind_mvar constants (box_term why3_goal)))
  in
  Why3_prover.prove ~show_goal:!Options.show_why3_goal why3_goal

let solve_invoke_why3 goal =
  let open Tactic in
  let* result = invoke_why3 goal in
  match result with
  | `Valid -> pure ()
  | _ -> fail "solve_invoke_why3: cannot solve goal"

module PureTactic = struct
  let ens_pure_intro name =
    let open Tactic in
    let* lhs = get_lhs in
    let* t, lhs =
      unwrap (unseq_open_ensures_opt lhs) "ens_pure_intro: not ensures"
    in
    let* _ = guard (Simply_typed.is_prop t) "ens_pure_intro: not prop" in
    let* _ = add_assumption name t in
    put_lhs lhs

  let req_pure_intro name =
    let open Tactic in
    let* rhs = get_rhs in
    let* t, rhs =
      unwrap (unseq_open_requires_opt rhs) "req_pure_intro: not requires"
    in
    let* _ = guard (Simply_typed.is_prop t) "req_pure_intro: not prop" in
    let* _ = add_assumption name t in
    put_rhs rhs

  let impl_intro name =
    let open Tactic in
    let* g = get_goal in
    let* p, q = unwrap (open_implies_opt g) "impl_intro: not implies" in
    let* _ = add_assumption name p in
    put_goal q

  let intro_pure name =
    let open Tactic in
    choices ~err:"intro_pure: failed"
      [impl_intro name; ens_pure_intro name; req_pure_intro name]

  let ens_pure_elim =
    let open Tactic in
    let* rhs = get_rhs in
    let* t, rhs =
      unwrap (unseq_open_ensures_opt rhs) "ens_pure_elim: not ensures"
    in
    let* _ = guard (Simply_typed.is_prop t) "ens_pure_elim: not prop" in
    let* result = invoke_why3 t in
    match result with
    | `Valid -> put_rhs rhs
    | _ -> fail "ens_pure_elim: cannot prove prop"

  let req_pure_elim =
    let open Tactic in
    let* lhs = get_lhs in
    let* t, lhs =
      unwrap (unseq_open_requires_opt lhs) "req_pure_elim: not requires"
    in
    let* _ = guard (Simply_typed.is_prop t) "req_pure_elim: not prop" in
    let* result = invoke_why3 t in
    match result with
    | `Valid -> put_lhs lhs
    | _ -> fail "req_pure_elim: cannot prove prop"
end

let parse_term ts =
  let open Tactic in
  let open Parsing.Parse in
  let* constants = get_constants in
  pure (parse_term ~ctx:constants ts)

let specialize name ts =
  let open Tactic in
  let* ts = map_m parse_term ts <&> Array.of_list in
  (* TODO allow not exactly same length? *)
  let* assumption = pop_assumption name in
  match assumption with
  | Forall b -> add_assumption name (msubst b ts)
  | _ -> fail "not a prop that can be specialised"

let have ~name s =
  let open Tactic in
  let* g = parse_term s in
  let* ps = pop_pctxt in
  let* _ = push_pctxt ps in
  let* _ = add_assumption name g in
  push_pctxt { ps with goal = g }

let axiom ~name s =
  let open Tactic in
  let* g = parse_term s in
  add_assumption name g

let case ~name s =
  let open Tactic in
  let* p = parse_term s in
  let* pc = pop_pctxt in
  let* _ = push_pctxt pc in
  let* _ = add_assumption name p in
  let* _ = push_pctxt pc in
  add_assumption name (Unop (Not, p))

let goal_is s =
  let open Tactic in
  let* g = parse_term s in
  let* g1 = get_goal in
  match equal_term g g1 with
  | true -> pure ()
  | false ->
      failf "@[<v>goal was expected to be@,  %a@,but was:@,  %a@]" pp_term g
        pp_term g1

let qed =
  let open Tactic in
  let* ps = get in
  match ps with
  | [] -> pure ()
  | _ -> fail "proof not finished"

let refl =
  let open Tactic in
  let* left, right = get_subsumption in
  if equal_term left right then pop_pctxt else fail "refl: cannot close goal"

let forall_intro =
  let open Tactic in
  let intro g k =
    match Prenex.prenex g with
    | Forall b ->
        let* ctxt = get_rename_ctxt in
        (* TODO freshness issues? this has to be free on both sides *)
        let xs, f, ctxt = unmbind_in ctxt b in
        let* _ = k f in
        let* _ = put_rename_ctxt ctxt in
        iter_array_m (fun x -> add_constant (name_of x) x) xs
    | _ -> fail "not a forall"
  in
  let staged =
    let* _, right = get_subsumption in
    intro right put_rhs
  in
  let pure =
    let* g = get_goal in
    intro g put_goal
  in
  choices [staged; pure]

let forall_elim t =
  let open Tactic in
  let* left, _ = get_subsumption in
  match Prenex.prenex left with
  | Forall b ->
      let* t = map_m parse_term t <&> Array.of_list in
      put_lhs (msubst b t)
  | _ -> fail "cannot eliminate forall"

let exists_intro t =
  let open Tactic in
  let* _, right = get_subsumption in
  match Prenex.prenex right with
  | Exists b ->
      let* t = map_m parse_term t <&> Array.of_list in
      put_rhs (msubst b t)
  | _ -> fail "cannot intro exists"

let exists_elim =
  let open Tactic in
  let* ctxt = get_rename_ctxt in
  let* left, _ = get_subsumption in
  match Prenex.prenex left with
  | Exists b ->
      let xs, f, ctxt = unmbind_in ctxt b in
      let* _ = put_lhs f in
      let* _ = put_rename_ctxt ctxt in
      iter_array_m (fun x -> add_constant (name_of x) x) xs
  | _ -> fail "cannot eliminate exists"

let conj_elim_l =
  let open Tactic in
  let* left, right = get_subsumption in
  match left with
  | Conj (a, _) ->
      let* ps = pop_pctxt in
      push_pctxt { ps with goal = Subsumes (a, right) }
  | _ -> fail "not a conjunction"

let conj_elim_r =
  let open Tactic in
  let* left, right = get_subsumption in
  match left with
  | Conj (_, b) ->
      let* ps = pop_pctxt in
      push_pctxt { ps with goal = Subsumes (b, right) }
  | _ -> fail "not a conjunction"

module DisjTactic = struct
  let disj_elim =
    let open Tactic in
    let* left, right = get_subsumption in
    match left with
    | Disj (a, b) ->
        let* ps = pop_pctxt in
        let* _ = push_pctxt { ps with goal = Subsumes (b, right) } in
        push_pctxt { ps with goal = Subsumes (a, right) }
    | _ -> fail "not a disjunction"

  let left =
    let open Tactic in
    let* left, right = get_subsumption in
    match right with
    | Disj (a, _) ->
        let* ps = pop_pctxt in
        push_pctxt { ps with goal = Subsumes (left, a) }
    | _ -> fail "not a disjunction"

  let right =
    let open Tactic in
    let* left, right = get_subsumption in
    match right with
    | Disj (_, b) ->
        let* ps = pop_pctxt in
        push_pctxt { ps with goal = Subsumes (left, b) }
    | _ -> fail "not a disjunction"
end

let simpl =
  let open Tactic in
  let* lhs, rhs = get_subsumption in
  put_subsumption (Simpl.simpl_term lhs) (Simpl.simpl_term rhs)

let req_left =
  let open Tactic in
  let* left, right = get_subsumption in
  match right with
  | Sequence (Requires h, rest) ->
      put_goal (Subsumes (Sequence (Ensures h, left), rest))
  | Requires h -> put_goal (Subsumes (Sequence (Ensures h, left), Ensures Emp))
  | _ -> fail "req_left cannot do anything"

module HeapTactic = struct
  let ens_heap_elim =
    let open Tactic in
    let* lhs = get_lhs in
    let* t, lhs =
      unwrap (unseq_open_ensures_opt lhs) "ens_heap_elim: not ensures"
    in
    let* ts =
      unwrap (Heap.deep_destruct_sepconj_opt t) "ens_heap_elim: not hprop"
    in
    let* _ = modify_heap_assumptions (List.append ts) in
    put_lhs lhs

  let req_heap_intro =
    let open Tactic in
    let* rhs = get_rhs in
    let* t, rhs =
      unwrap (unseq_open_requires_opt rhs) "req_heap_intro: not requires"
    in
    let* ts =
      unwrap (Heap.deep_destruct_sepconj_opt t) "req_heap_intro: not hprop"
    in
    let* _ = modify_heap_assumptions (List.append ts) in
    put_rhs rhs

  let intro_heap =
    let open Tactic in
    choices ~err:"failed to intro heap" [ens_heap_elim; req_heap_intro]

  let unseq_open_opt f target =
    let open Util.Options.Monad in
    let* t, target = f target in
    let+ ts = Heap.deep_destruct_sepconj_opt t in
    (ts, target)

  let rec unseq_open_loop f target =
    match unseq_open_opt f target with
    | None -> ([], target)
    | Some (ts1, target) ->
        let ts2, target = unseq_open_loop f target in
        (ts1 @ ts2, target)

  let ens_heap_intros =
    let open Tactic in
    let* lhs = get_lhs in
    let ts, lhs = unseq_open_loop unseq_open_ensures_opt lhs in
    let* _ = modify_heap_assumptions (List.append ts) in
    put_lhs lhs

  let req_heap_intros =
    let open Tactic in
    let* rhs = get_rhs in
    let ts, rhs = unseq_open_loop unseq_open_requires_opt rhs in
    let* _ = modify_heap_assumptions (List.append ts) in
    put_rhs rhs

  let intros_heap =
    let open Tactic in
    let* _ = ens_heap_intros in
    req_heap_intros

  let req_heap_elim_common =
    let open Tactic in
    let* lhs = get_lhs in
    let* t, lhs =
      unwrap (unseq_open_requires_opt lhs) "req_heap_elim: not requires"
    in
    let* ts =
      unwrap (Heap.deep_destruct_sepconj_opt t) "req_heap_elim: not hprop"
    in
    let* heap_assumptions = get_heap_assumptions in
    let ts, heap_assumptions, equalities = Heap.biab_list ts heap_assumptions in
    let+ _ = guard (List.is_empty ts) "req_heap_elim: cannot prove hprop" in
    (heap_assumptions, lhs, equalities)

  let req_heap_elim =
    let open Tactic in
    let* heap_assumptions, lhs, equalities = req_heap_elim_common in
    let* _ = put_heap_assumptions heap_assumptions in
    let* _ = put_lhs lhs in
    let* p = get_pctxt in
    iter_m (fun equality -> push_pctxt { p with goal = equality }) equalities

  let solve_req_heap_elim =
    let open Tactic in
    let* heap_assumptions, lhs, equalities = req_heap_elim_common in
    let tactic =
      let* _ = iter_m solve_invoke_why3 equalities in
      let* _ = put_heap_assumptions heap_assumptions in
      put_lhs lhs
    in
    catch tactic (fun _ -> fail "solve_req_heap_elim: cannot prove equality")

  let ens_heap_intro_common =
    let open Tactic in
    let* rhs = get_rhs in
    let* t, rhs =
      unwrap (unseq_open_ensures_opt rhs) "ens_heap_intro: not ensures"
    in
    let* ts =
      unwrap (Heap.deep_destruct_sepconj_opt t) "ens_heap_intro: not hprop"
    in
    let* heap_assumptions = get_heap_assumptions in
    let ts, heap_assumptions, equalities = Heap.biab_list ts heap_assumptions in
    let+ _ = guard (List.is_empty ts) "ens_heap_intro: cannot prove hprop" in
    (heap_assumptions, rhs, equalities)

  let ens_heap_intro =
    let open Tactic in
    let* heap_assumptions, rhs, equalities = ens_heap_intro_common in
    let* _ = put_heap_assumptions heap_assumptions in
    let* _ = put_rhs rhs in
    let* p = get_pctxt in
    iter_m (fun equality -> push_pctxt { p with goal = equality }) equalities

  let solve_ens_heap_intro =
    let open Tactic in
    let* heap_assumptions, rhs, equalities = ens_heap_intro_common in
    let tactic =
      let* _ = iter_m solve_invoke_why3 equalities in
      let* _ = put_heap_assumptions heap_assumptions in
      put_rhs rhs
    in
    catch tactic (fun _ -> fail "solve_ens_heap_intro: cannot prove equality")

  let heap_solver =
    let open Tactic in
    let rec loop () =
      let* goal = get_goal in
      let* _ = intros_heap in
      let* _ = try_ solve_req_heap_elim in
      let* _ = try_ solve_ens_heap_intro in
      let* goal' = get_goal in
      if equal_term goal goal' then pure () else loop ()
    in
    loop ()

  let revert_heap =
    let open Tactic in
    let* heap_assumptions = get_heap_assumptions in
    let* lhs = get_lhs in
    let* _ =
      put_lhs (Sequence (Ensures (Constr.sepconj heap_assumptions), lhs))
    in
    put_heap_assumptions []
end

let prove =
  let open Tactic in
  let prove_with_ctx p =
    let* assumptions = get_assumptions in
    let p =
      let ass =
        SMap.bindings assumptions |> List.map snd
        |> List.filter Why3_prover.is_translatable
      in
      List.fold_right (fun c t -> Implies (c, t)) ass p
    in
    let* free = get_constants in
    let entail =
      let free = free |> SMap.bindings |> List.map snd |> Array.of_list in
      unbox (Mk.forall (bind_mvar free (box_term p)))
    in
    let res = Why3_prover.prove ~show_goal:!Options.show_why3_goal entail in
    (match res with
    | `Valid -> Format.printf "==> Valid\n@."
    | `Invalid -> Format.printf "==> Invalid\n@."
    | `Unknown s ->
        Format.printf "==> Unknown: %s\n@." s
        (* | `Failure s -> Format.printf "==> Failure: %s\n@." s *));
    pure res
  in
  let ens_right =
    let* left, right = get_subsumption in
    let* p, f1 = uncons_ens right in
    let* res = prove_with_ctx p in
    match res with
    | `Valid -> put_goal (Subsumes (left, f1))
    | _ -> fail "could not prove ens on the right"
  in
  let req_left =
    let* left, right = get_subsumption in
    let* p, f1 = uncons_req left in
    let* res = prove_with_ctx p in
    match res with
    | `Valid -> put_goal (Subsumes (f1, right))
    | _ -> fail "could not prove req on the left"
  in
  let both_values =
    let could_be_value t =
      match t with
      | Var _ | True | False | Unit | Int _ | Apply _ -> true
      | _ -> false
    in
    let* left, right = get_subsumption in
    match could_be_value left && could_be_value right with
    | false -> fail "not values"
    | true ->
        let* res = prove_with_ctx (Binop (Eq, left, right)) in
        (match res with
        | `Valid ->
            let* _ = pop_pctxt in
            pure ()
        | _ -> fail "could not prove equality")
  in
  let can_be_translated =
    (* this is more general than the value case *)
    (* TODO is it possible that this produces props, which should then be related using implies? *)
    let* left, right = get_subsumption in
    match Why3_prover.(is_translatable left && is_translatable right) with
    | false -> fail "cannot be translated"
    | true ->
        let* res = prove_with_ctx (Binop (Eq, left, right)) in
        (match res with
        | `Valid ->
            let* _ = pop_pctxt in
            pure ()
        | _ -> fail "could not prove")
  in
  let is_prop =
    let rec could_be_prop t =
      match t with
      | True | False | Apply _ -> true
      | Binop ((Ge | Gt | Eq | Neq | Le | Lt), _, _) -> true
      | Implies (a, b) | Conj (a, b) | Disj (a, b) ->
          could_be_prop a && could_be_prop b
      | _ -> false
    in
    let* g = get_goal in
    match could_be_prop g with
    | false -> fail "not a prop"
    | true ->
        let* res = prove_with_ctx g in
        (match res with
        | `Valid ->
            let* _ = pop_pctxt in
            pure ()
        | _ -> fail "could not prove goal")
  in
  choices ~err:"failed to prove pure obligation"
    [
      both_values;
      is_prop;
      ens_right;
      req_left;
      (* ens_ens; req_req;*)
      can_be_translated;
    ]

(* TODO: refactor into some top-level module, with a different name. The current
   name clashes with Pstate -> proof_state *)
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
    let sym, def = open_dfun (Parsing.Parse.parse_decl decl) in
    try
      set_definitions (add_decl sym def !current_state.definitions);
      Format.printf "%s declared@." sym.sym_name
    with Failure msg -> Format.printf "error: %s@." msg

  let start_proof g =
    set_goals [Proof_context.create ~goal:(Parsing.Parse.parse_term g)];
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

  let have ~name = make_interactive (have ~name)
  let case ~name = make_interactive (case ~name)
  let axiom ~name = make_interactive (axiom ~name)
  let goal_is = make_interactive goal_is
  let qed = make_interactive (fun () -> qed)
  let specialize h = make_interactive (specialize h)
  let refl () = run_tactic refl
  let req_heap_intro () = run_tactic HeapTactic.req_heap_intro
  let ens_heap_intro () = run_tactic HeapTactic.ens_heap_intro
  let req_heap_elim () = run_tactic HeapTactic.req_heap_elim
  let ens_heap_elim () = run_tactic HeapTactic.ens_heap_elim
  let intro_pure name = run_tactic (PureTactic.intro_pure name)
  let intro_heap () = run_tactic HeapTactic.intro_heap
  let intros_heap () = run_tactic HeapTactic.intros_heap
  let revert_heap () = run_tactic HeapTactic.revert_heap
  let heap_solver () = run_tactic HeapTactic.heap_solver
  let forall_intro = make_interactive (fun () -> forall_intro)
  let forall_elim = make_interactive forall_elim
  let exists_intro = make_interactive exists_intro
  let exists_elim = make_interactive (fun () -> exists_elim)
  let disj_elim () = run_tactic DisjTactic.disj_elim
  let left () = run_tactic DisjTactic.left
  let right () = run_tactic DisjTactic.right
  let conj_elim_l () = run_tactic conj_elim_l
  let conj_elim_r () = run_tactic conj_elim_r
  let simpl () = run_tactic simpl
  let req_left = make_interactive (fun () -> req_left)

  (* let cancel_heap = make_interactive (fun () -> cancel_heap) *)
  let prove = make_interactive (fun () -> prove)
  let admit () = run_tactic admit
  let dup () = run_tactic dup

  (* let induction ~ih = make_interactive (induction ~ih) *)
  let prove_s s = Why3_prover.prove ~show_goal:true (Parsing.Parse.parse_prop s)

  (** Unfold a definition (symbol) on both side of a sequent in the current
      proof state.

      TODO: implement `unfold in`. TODO: report failure using monad. Make it
      consistent *)
  let unfold (sym_name : string) =
    let sym = { sym_name } in
    let definitions = get_definitions () in
    let open Tactic in
    match SymMap.find_opt sym definitions with
    | None -> Format.printf "unfold: the symbol %s does not exist@." sym_name
    | Some def -> run_tactic (modify_goal (Unfold.unfold sym def))

  (** Generate an induction hypothesis in the current proof state. *)
  let induction :
      ?vars:string list ->
      name:string ->
      [ `List | `Int of int ] ->
      string ->
      unit =
   fun ?(vars = []) ~name kind x ->
    let tac =
      let open Tactic in
      let* assumptions = get_assumptions in
      let* x = get_constant x in
      let* vars = map_m get_constant vars in
      let* lhs, rhs = get_subsumption in
      let assumptions = List.map snd (SMap.bindings assumptions) in
      let vars = Array.of_list vars in
      (* generate the body of the induction hypothesis *)
      let ih_body = Induction.induction kind x vars assumptions lhs rhs in
      (* and wrap it into a prop *)
      let ih_prop = Forall ih_body in
      add_assumption name ih_prop
    in
    run_tactic tac

  (* TODO: implement `rewrite in` (but where can we safely rewrite?) *)

  (** Rewrite in the LHS of a sequent. *)
  let rewrite (h : string) =
    let tac =
      let open Tactic in
      let* assumption = get_assumption h in
      let rule = Rewrite.prop_to_rule assumption in
      let* lhs, _ = get_subsumption in
      match Rewrite.rewrite rule lhs with
      | Some (lhs1, side) ->
          let* ps = pop_pctxt in
          let* () = push_pctxt ps in
          let* () = put_lhs lhs1 in
          iter_m (fun p -> push_pctxt { ps with goal = p }) (List.rev side)
      | None -> fail "rewrite failed"
    in
    run_tactic tac
end
