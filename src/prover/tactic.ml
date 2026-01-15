open Core.Syntax
open Core.Pretty
open Core.Decl
open Core.Syntax_util
open Core.Simply_typed
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

module Pctx = struct
  type t = {
    rename_ctxt : Bindlib.ctxt;
    constants : term var SMap.t;
    assumptions : term SMap.t;
    heap_assumptions : term list; (* TODO: add names *)
    goal : term;
  }

  let create ~goal () =
    {
      rename_ctxt = empty_ctxt; (* simple solution for now. *)
      constants = SMap.empty;
      assumptions = SMap.empty;
      heap_assumptions = [];
      goal;
    }

  let draw_line n = String.make n '-'

  (* TODO: use rename_ctxt *)
  let pp ppf { rename_ctxt = _; constants; assumptions; heap_assumptions; goal } =
    Fmt.pf ppf "@[<v>@[<hov>%a@]@,"
      Fmt.(list ~sep:comma Fmt.string)
      (List.map fst (SMap.bindings constants));
    (match SMap.is_empty assumptions with
    | true -> ()
    | false ->
        Fmt.pf ppf "%a@,"
          (pp_hypotheses ~pp_k:Fmt.string ~pp_v:pp_term)
          assumptions);
    (* always draw the line, even if there are no hypotheses *)
    let line_length = 40 in
    let line = draw_line line_length in
    Fmt.pf ppf "%s@," line;
    (match heap_assumptions with
    | [] -> ()
    | _ ->
        let heap_line = draw_line (line_length - 1) ^ "*" in
        Fmt.pf ppf "%a@,%s@," Fmt.(list ~sep:cut pp_term) heap_assumptions heap_line);
    (match goal with
    | Subsumes (l, r) -> Fmt.pf ppf "   %a@,<: %a" pp_term l pp_term r
    | _ -> Fmt.pf ppf "%a" pp_term goal);
    Fmt.pf ppf "@]"

  (* let _pp ppf
      { rename_ctxt = _; constants = _; assumptions; heap_context = _; goal } =
    let hyp =
      match SMap.is_empty assumptions with
      | true -> ""
      | false ->
          Fmt.str "%a"
            (pp_hypotheses ~pp_k:Fmt.string ~pp_v:pp_term)
            assumptions
    in
    let goal =
      match goal with
      | Subsumes (l, r) -> Fmt.str "   %a<: 1%a" pp_term l pp_term r
      | Implies (l, r) -> Fmt.str "   %a=> %a" pp_term l pp_term r
      | _ -> Fmt.str "%a" pp_term goal
    in
    (* TODO no way to show ---* *)
    Fmt.pf ppf "%a" PrintBox_text.pp PrintBox.(vlist [text hyp; text goal]) *)
end

module Pstate = struct
  type t = Pctx.t list

  let pp ppf s =
    match s with
    | [] -> Fmt.pf ppf "no more goals"
    | g :: gs ->
        Fmt.pf ppf "@[<v>@,%a" Pctx.pp g;
        (match List.length gs with
        | 0 -> ()
        | n -> Fmt.pf ppf "@,(%d more goals)" n);
        Fmt.pf ppf "@,@]"
end

module Tactic : sig
  type 'a t

  val run : 'a t -> Pstate.t -> (Pstate.t, string) result
  (* basic combinators *)
  val return : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val fail : string -> 'a t
  val failf : ('a, Format.formatter, unit, 'b t) format4 -> 'a
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
  (* derived combinators: managing goals *)
  val pop : Pctx.t t
  val push : Pctx.t -> unit t
  val get_pctxt : Pctx.t t
  val put_pctxt : Pctx.t -> unit t
  val gets_pctxt : (Pctx.t -> 'a) -> 'a t
  val modify_pctxt : (Pctx.t -> Pctx.t) -> unit t
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
end = struct
  type 'a t = Pstate.t -> ('a * Pstate.t, string) Result.t

  let run m s = Result.map snd (m s)
  let fail s = fun _ -> Error s
  let failf fmt = Format.kasprintf (fun s -> fun _ -> Error s) fmt
  let return x = fun s -> Ok (x, s)
  let map = fun f m -> fun s -> Result.map (fun (a, s1) -> (f a, s1)) (m s)
  let bind m f = fun s -> Result.bind (m s) (fun (x, s') -> f x s')
  let ( let+ ) a f = map f a
  let ( let* ) = bind

  let choice t1 t2 =
   fun ps ->
    match t1 ps with
    | Error _ -> t2 ps
    | Ok s -> Ok s

  let rec choices ?(err = "empty choice") ts =
   fun ps ->
    match ts with
    | [] -> Error err
    | t :: ts1 ->
        (match t ps with
        | Error er ->
            choices ~err ts1 ps
            (* TODO possibly use a list or tree of errors *)
            |> Result.map_error (fun e -> Format.asprintf "%s / %s" e er)
        | Ok a -> Ok a)

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

  let catch m h =
    fun s ->
      let r = m s in
      match m s with
      | Ok _ -> r
      | Error e -> h e s

  let get = fun s -> Ok (s, s)

  let put s = fun _ -> Ok ((), s)

  let gets f = fun s -> Ok (f s, s)

  let modify f = fun s -> Ok ((), f s)

  open Pctx

  let pop =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | p :: ps ->
        let+ _ = put ps in
        p

  let push p = modify (fun ps -> p :: ps)

  let get_pctxt =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | p :: _ -> return p

  let put_pctxt p =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | _ :: ps -> put (p :: ps)

  let gets_pctxt f =
    let* ps = get in
    match ps with
    | [] -> fail "no more goal"
    | p :: _ -> return (f p)

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
    | Some v -> return v

  let get_assumption name =
    let* assumptions = get_assumptions in
    match SMap.find_opt name assumptions with
    | None -> fail ("no assumption named: " ^ name)
    | Some t -> return t

  (* let get_heap_assumption name =
    let* heap_assumptions = get_heap_assumptions in
    match SMap.find_opt name heap_assumptions with
    | None -> fail ("no heap assumption named: " ^ name)
    | Some t -> return t *)

  let put_rename_ctxt rename_ctxt =
    modify_pctxt (fun p -> { p with rename_ctxt })

  let put_constants constants =
    modify_pctxt (fun p -> { p with constants })

  let put_assumptions assumptions =
    modify_pctxt (fun p -> { p with assumptions })

  let put_heap_assumptions heap_assumptions =
    modify_pctxt (fun p -> { p with heap_assumptions })

  let put_goal goal =
    modify_pctxt (fun p -> { p with goal })

  let add_constant name v =
    let* constants = get_constants in
    if SMap.mem name constants
    then fail ("add_constant: " ^ name ^ " is already used")
    else put_constants (SMap.add name v constants)

  let add_assumption name t =
    let* assumptions = get_assumptions in
    if SMap.mem name assumptions
    then fail ("add_assumption: " ^ name ^ " is already used")
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
  let+ _ = pop in
  ()

let uncons_ens f =
  let open Tactic in
  match f with
  | Sequence (Ensures p, rest) when is_pure p -> return (p, rest)
  | Ensures p when is_pure p -> return (p, Ensures Emp)
  | _ -> fail "cannot uncons pure ens"

let uncons_req f =
  let open Tactic in
  match f with
  | Sequence (Requires p, rest) when is_pure p -> return (p, rest)
  | Requires p when is_pure p -> return (p, Requires Emp)
  | _ -> fail "cannot uncons pure req"

let get_subsumption =
  let open Tactic in
  let* g = get_goal in
  match g with
  | Subsumes (left, right) -> return (left, right)
  | _ -> failf "not a subsumption: %a" Core.Pretty.pp_term g

let put_lhs l =
  let open Tactic in
  let* _, right = get_subsumption in
  put_goal (Subsumes (l, right))

let put_rhs r =
  let open Tactic in
  let* left, _ = get_subsumption in
  put_goal (Subsumes (left, r))

let intro_pure name =
  let open Tactic in
  let* left, right = get_subsumption in
  let intro_left =
    let* p, rest = uncons_ens left in
    let* _ = put_lhs rest in
    add_assumption name p
  in
  let intro_right =
    let* p, rest = uncons_req right in
    let* _ = put_rhs rest in
    add_assumption name p
  in
  choices ~err:"failed to intro pure" [intro_left; intro_right]

(* let intro_heap =
  let open Tactic in
  let* left, right = get_subsumption in
  let intro_left =
    let* h, rest = uncons_hens left in
    match h with
    | Emp -> fail "cannot uncons empty"
    | _ ->
        let* () = put_lhs rest in
        add_heap_assumption h
  in
  let intro_right =
    let* h, rest = uncons_hreq right in
    match h with
    | Emp -> fail "cannot uncons empty"
    | _ ->
        let* () = put_rhs rest in
        add_heap_assumption h
  in
  choices ~err:"failed to intro heap" [intro_left; intro_right] *)

let specialize name ts =
  let open Tactic in
  (* TODO: parse_term with respect to constant context *)
  let ts = List.map parse_term ts |> Array.of_list in
  (* TODO allow not exactly same length? *)
  let* assumption = pop_assumption name in
  match assumption with
  | Forall b -> add_assumption name (msubst b ts)
  | _ -> fail "not a prop that can be specialised"

let refl =
  let open Tactic in
  let* left, right = get_subsumption in
  if equal_term left right then pop
  else fail "cannot close goal using reflexivity"

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
      (* TODO: parse_term with respect to constant context *)
      let t = List.map parse_term t |> Array.of_list in
      put_lhs (msubst b t)
  | _ -> fail "cannot eliminate forall"

let exists_intro t =
  let open Tactic in
  let* _, right = get_subsumption in
  match Prenex.prenex right with
  | Exists b ->
      (* TODO: parse_term with respect to constant context *)
      let t = List.map parse_term t |> Array.of_list in
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

let disj_elim =
  let open Tactic in
  let* left, right = get_subsumption in
  match left with
  | Disj (a, b) ->
      let* ps = pop in
      let* _ = push { ps with goal = Subsumes (b, right) } in
      push { ps with goal = Subsumes (a, right) }
  | _ -> fail "not a disjunction"

let left =
  let open Tactic in
  let* left, right = get_subsumption in
  match right with
  | Disj (a, _) ->
      let* ps = pop in
      push { ps with goal = Subsumes (left, a) }
  | _ -> fail "not a disjunction"

let right =
  let open Tactic in
  let* left, right = get_subsumption in
  match right with
  | Disj (_, b) ->
      let* ps = pop in
      push { ps with goal = Subsumes (left, b) }
  | _ -> fail "not a disjunction"

let simpl =
  let open Tactic in
  let* left, right = get_subsumption in
  put_goal (Subsumes (Simpl.simpl_term left, Simpl.simpl_term right))

let req_left =
  let open Tactic in
  let* left, right = get_subsumption in
  match right with
  | Sequence (Requires h, rest) ->
      put_goal (Subsumes (Sequence (Ensures h, left), rest))
  | Requires h -> put_goal (Subsumes (Sequence (Ensures h, left), Ensures Emp))
  | _ -> fail "req_left cannot do anything"

module HeapTactic = struct
  (* TODO: catch Invalid_argument that may be thrown by Heap functions *)

  let ens_heap_intro =
    let open Tactic in
    let* _, right = get_subsumption in
    match unseq_open_ensures_opt right with
    | None -> fail "ens_heap_intro: not ensures"
    | Some (t, _) when not (is_hprop t) -> fail "ens_heap_intro: not hprop"
    | Some (t, right) ->
        let ts = Heap.deep_destruct_sepconj t in
        let* heap_assumptions = get_heap_assumptions in
        let* _ = put_heap_assumptions (ts @ heap_assumptions) in
        put_rhs right

  let req_heap_intro =
    let open Tactic in
    let* left, _ = get_subsumption in
    match unseq_open_requires_opt left with
    | None -> fail "req_heap_intro: not requires"
    | Some (t, _) when not (is_hprop t) -> fail "req_heap_intro: not hprop"
    | Some (t, left) ->
        let ts = Heap.deep_destruct_sepconj t in
        let* heap_assumptions = get_heap_assumptions in
        let* _ = put_heap_assumptions (ts @ heap_assumptions) in
        put_lhs left

  let rec unseq_open_loop f target =
    match f target with
    | None -> [], target
    | Some (t, _) when not (is_hprop t) -> [], target
    | Some (t, target) ->
        let ts, target = unseq_open_loop f target in
        Heap.deep_destruct_sepconj t @ ts, target

  let ens_heap_intros =
    let open Tactic in
    let* _, right = get_subsumption in
    let ts, right = unseq_open_loop unseq_open_ensures_opt right in
    let* heap_assumptions = get_heap_assumptions in
    let* _ = put_heap_assumptions (ts @ heap_assumptions) in
    put_rhs right

  let req_heap_intros =
    let open Tactic in
    let* left, _ = get_subsumption in
    let ts, left = unseq_open_loop unseq_open_requires_opt left in
    let* heap_assumptions = get_heap_assumptions in
    let* _ = put_heap_assumptions (ts @ heap_assumptions) in
    put_lhs left

  let req_heap_elim : unit Tactic.t =
    let open Tactic in
    let* _, right = get_subsumption in
    match unseq_open_requires_opt right with
    | None -> fail "req_heap_elim: not requires"
    | Some (t, _) when not (is_hprop t) -> fail "req_heap_elim: not hprop"
    | Some (t, right) ->
        let* heap_assumptions = get_heap_assumptions in
        let ts = Heap.deep_destruct_sepconj t in
        let ts, heap_assumptions, equalities = Heap.biab_list ts heap_assumptions in
        match ts with
        | [] ->
            let* _ = put_heap_assumptions heap_assumptions in
            let* _ = put_rhs right in
            let* p = get_pctxt in (* TODO: is there a more elegant way to write this? *)
            iter_m (fun equality -> push {p with goal = equality}) equalities
        | _ -> fail "req_heap_elim: cannot prove hprop"


  let ens_heap_elim : unit Tactic.t =
    let open Tactic in
    let* left, _ = get_subsumption in
    match unseq_open_ensures_opt left with
    | None -> fail "ens_heap_elim: not ensures"
    | Some (t, _) when not (is_hprop t) -> fail "ens_heap_elim: not hprop"
    | Some (t, left) ->
        let* heap_assumptions = get_heap_assumptions in
        let ts = Heap.deep_destruct_sepconj t in
        let ts, heap_assumptions, equalities = Heap.biab_list ts heap_assumptions in
        match ts with
        | [] ->
            let* _ = put_heap_assumptions heap_assumptions in
            let* _ = put_lhs left in
            let* p = get_pctxt in (* TODO: is there a more elegant way to write this? *)
            iter_m (fun equality -> push {p with goal = equality}) equalities
        | _ -> fail "req_heap_elim: cannot prove hprop"

  (* automation: do later *)
  let heap_solver () = failwith "todo"
end

(* let cancel_heap =
  let open Tactic in
  let* left, right = get_subsumption in
  let ens_ens =
    let* h1, f1 = uncons_hens left in
    let* h2, f2 = uncons_hens right in
    let a, f = Heap.biab h1 h2 in
    Constr.(put_goal (Subsumes (ens_seq f f1, ens_seq a f2)))
  in
  let req_req =
    let* h1, f1 = uncons_hreq right in
    let* h2, f2 = uncons_hreq left in
    let a, f = Heap.biab h1 h2 in
    Constr.(put_goal (Subsumes (req_seq a f1, req_seq f f2)))
  in
  let ens_req_left =
    (* TODO quantifier? *)
    match left with
    | Sequence (Ensures h1, Sequence (Requires h2, rest)) ->
        let a, f = Heap.biab h1 h2 in
        put_lhs (Constr.sequence [Requires a; Ensures f; rest])
    | _ -> fail "cannot match"
  in
  let ctx_req_left =
    let* h2, f1 = uncons_hreq left in
    let* h1 = get_heap_assumptions in
    let a, f = Heap.biab h1 h2 in
    let* () = put_heap_assumptions f in
    put_lhs (Constr.req_seq a f1)
  in
  let ctx_ens_right =
    let* h2, f1 = uncons_hens right in
    let* h1 = get_heap_assumptions in
    let a, f = Heap.biab h1 h2 in
    let* () = put_heap_assumptions f in
    put_rhs (Constr.ens_seq a f1)
  in
  (* TODO xpure? *)
  choices ~err:"failed to cancel heap"
    [ens_ens; req_req; ens_req_left; ctx_req_left; ctx_ens_right] *)

let prove =
  let open Tactic in
  let prove_with_ctx p =
    let* pure = get_assumptions in
    let pure =
      SMap.bindings pure |> List.map snd
      |> List.filter Why3_prover.is_translatable
      |> Core.Syntax.Constr.conj
    in
    let* free = get_constants in
    let entail =
      let free = free |> SMap.bindings |> List.map snd |> Array.of_list in
      unbox (Mk.forall (bind_mvar free (box_term (Implies (pure, p)))))
    in
    let res = Why3_prover.prove entail in
    (match res with
    | `Valid -> Format.printf "==> Valid\n@."
    | `Invalid -> Format.printf "==> Invalid\n@."
    | `Unknown s ->
        Format.printf "==> Unknown: %s\n@." s
        (* | `Failure s -> Format.printf "==> Failure: %s\n@." s *));
    return res
  in
  (* let ens_ens =
    let* p1, f1 = uncons_ens left in
    let* p2, f2 = uncons_ens right in
    let* res = prove_with_ctx (Implies (p1, p2)) in
    match res with
    | `Valid -> put_goal (Subsumes (f1, f2))
    | _ -> fail "could not cancel ens"
  in
  let req_req =
    let* p1, f1 = uncons_ens right in
    let* p2, f2 = uncons_ens left in
    let* res = prove_with_ctx (Implies (p1, p2)) in
    match res with
    | `Valid -> put_goal (Subsumes (f2, f1))
    | _ -> fail "could not cancel req"
  in *)
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
            let* _ = pop in
            return ()
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
            let* _ = pop in
            return ()
        | _ -> fail "could not prove")
  in
  let is_prop =
    let rec could_be_prop t =
      match t with
      | True | False | Apply _ -> true
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
            let* _ = pop in
            return ()
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

  let start_proof g =
    set_goals [Pctx.create ~goal:(parse_staged_spec g) ()];
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
  (* let intro_heap = make_interactive (fun () -> intro_heap) *)
  (* let revert_heap = make_interactive (fun () -> revert_heap) *)
  let req_heap_intro = make_interactive (fun () -> HeapTactic.req_heap_intro)
  let ens_heap_intro = make_interactive (fun () -> HeapTactic.ens_heap_intro)
  let req_heap_elim = make_interactive (fun () -> HeapTactic.req_heap_elim)
  let ens_heap_elim = make_interactive (fun () -> HeapTactic.ens_heap_elim)
  (* TODO: write an "intro heap" tactic *)
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
  (* let cancel_heap = make_interactive (fun () -> cancel_heap) *)
  let prove = make_interactive (fun () -> prove)
  let admit = make_interactive (fun () -> admit)

  (* let induction ~ih = make_interactive (induction ~ih) *)
  let prove_s s = Why3_prover.prove (parse_prop s)

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
          let* lhs, rhs = get_subsumption in
          put_goal
            (Subsumes (Unfold.unfold sym def lhs, Unfold.unfold sym def rhs))
        in
        run_tactic tac

  (** Generate an induction hypothesis in the current proof state.

      TODO: add decreasing measurement as a hypothesis for the IH. *)
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
      let lhs1, side = Rewrite.rewrite rule lhs in
      let* ps = pop in
      let* () = push ps in
      let* () = put_lhs lhs1 in
      iter_m (fun p -> push { ps with goal = p }) (List.rev side)
    in
    run_tactic tac
end
