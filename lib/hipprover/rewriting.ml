open Hipcore
open Hiptypes
open Pretty
open Debug

let ( let* ) = Option.bind
let ( let+ ) a f = Option.map f a

let rec sequence f xs =
  match xs with
  | [] -> Some []
  | x :: xs1 ->
    let* x1 = f x in
    let* xs2 = sequence f xs1 in
    Some (x1 :: xs2)

let sequence2 f xs ys = List.map2 (fun x y -> (x, y)) xs ys |> sequence f

type uterm =
  | Staged of staged_spec
  | Pure of pi
  | Heap of kappa
  | Term of term
  | Binder of string

let string_of_uterm t =
  match t with
  | Staged s -> string_of_staged_spec s
  | Pure p -> string_of_pi p
  | Heap h -> string_of_kappa h
  | Term t -> string_of_term t
  | Binder s -> s

(* let string_of_uterm t =
  match t with
  | Staged s -> "Staged " ^ string_of_staged_spec s
  | Pure p -> "Pure " ^ string_of_pi p
  | Heap h -> "Heap " ^ string_of_kappa h
  | Term t -> "Term " ^ string_of_term t
  | Binder s -> "Binder " ^ s *)

let uterm_to_staged = function
  | Staged s -> s
  | u -> failwith (Format.asprintf "not staged: %s" (string_of_uterm u))

let uterm_to_pure = function
  | Pure p -> p
  | u -> failwith (Format.asprintf "not pure: %s" (string_of_uterm u))

let uterm_to_heap = function
  | Heap h -> h
  | u -> failwith (Format.asprintf "not heap: %s" (string_of_uterm u))

let uterm_to_term = function
  | Term t -> t
  | u -> failwith (Format.asprintf "not term: %s" (string_of_uterm u))

let uterm_to_binder = function
  | Binder s -> s
  | u -> failwith (Format.asprintf "not binder: %s" (string_of_uterm u))

module UF : sig
  type t
  type store

  val new_store : unit -> store
  val copy : store -> store
  val make : store -> uterm option -> t
  val get : store -> t -> uterm option
  val set : store -> t -> uterm option -> unit
  val eq : store -> t -> t -> bool
  val union : store -> t -> t -> unit
end = struct
  module Store = UnionFind.StoreMap
  include UnionFind.Make (Store)

  type c = uterm option
  type t = c rref
  type nonrec store = c store

  let new_store () = Store.new_store ()
  let copy = Store.copy
  let union s a b = ignore (union s a b)
end

(* unification variables are encoded in the AST with string names *)

(** a string that we can tokenise, but not something likely to appear in
    programs or generated code *)
let var_prefix = "__"

let is_uvar_name f = String.starts_with ~prefix:var_prefix f
let uvar_staged n = HigherOrder (var_prefix ^ n, [])
let uvar_heap n = PointsTo (var_prefix ^ n, Const ValUnit)
let uvar_pure n = Predicate (var_prefix ^ n, [])
let uvar_term n = Var (var_prefix ^ n)
let uvar_binder n = var_prefix ^ n

let get_uvar = function
  | Staged (HigherOrder (f, _)) when is_uvar_name f -> Some f
  | Pure (Predicate (f, _)) when is_uvar_name f -> Some f
  | Heap (PointsTo (f, _)) when is_uvar_name f -> Some f
  | Term (Var f) when is_uvar_name f -> Some f
  | Binder f when is_uvar_name f -> Some f
  | _ -> None

(* to avoid having a constructor for UF.t in the AST, use a layer of indirection *)
type 'a unif = 'a * UF.t SMap.t
type unifiable = uterm unif

let to_unifiable st f : unifiable =
  let@ _ =
    span (fun r ->
        debug ~at:99 ~title:"to_unifiable" "%s"
          (string_of_result
             (fun (ut, e) ->
               Format.asprintf "%s & %s" (string_of_uterm ut)
                 (string_of_list Fun.id (SMap.keys e)))
             r))
  in
  let visitor =
    object (self)
      inherit [_] mapreduce_spec as super
      method zero = SMap.empty
      method plus = SMap.merge_arbitrary

      method! visit_HigherOrder () f v =
        (* both a variable and something which may contain binder variables... *)
        match v with
        | [] ->
          if is_uvar_name f then
            (HigherOrder (f, []), SMap.singleton f (UF.make st None))
          else (HigherOrder (f, []), SMap.empty)
        | _ :: _ ->
          let v1, e = super#visit_HigherOrder () f v in
          if is_uvar_name f then (v1, SMap.add f (UF.make st None) e)
          else (v1, e)

      method! visit_Predicate () f v =
        let v1, e = self#visit_list self#visit_term () v in
        if is_uvar_name f then
          (Predicate (f, v1), SMap.add f (UF.make st None) e)
        else (Predicate (f, v1), e)

      method! visit_PointsTo () l v =
        let v1, e = self#visit_term () v in
        if is_uvar_name l then (PointsTo (l, v1), SMap.add l (UF.make st None) e)
        else (PointsTo (l, v1), e)

      method! visit_Var () x =
        if is_uvar_name x then (Var x, SMap.singleton x (UF.make st None))
        else (Var x, SMap.empty)

      (* binders *)
      method! visit_Bind () x f1 f2 =
        let v1, e = super#visit_Bind () x f1 f2 in
        if is_uvar_name x then (v1, SMap.add x (UF.make st None) e) else (v1, e)

      method! visit_Exists () x f =
        let v1, e = super#visit_Exists () x f in
        if is_uvar_name x then (v1, SMap.add x (UF.make st None) e) else (v1, e)

      method! visit_ForAll () x f =
        let v1, e = super#visit_ForAll () x f in
        if is_uvar_name x then (v1, SMap.add x (UF.make st None) e) else (v1, e)
    end
  in
  match f with
  | Staged s ->
    let s, e = visitor#visit_staged_spec () s in
    (Staged s, e)
  | Pure p ->
    let p, e = visitor#visit_pi () p in
    (Pure p, e)
  | Heap h ->
    let h, e = visitor#visit_kappa () h in
    (Heap h, e)
  | Term t ->
    let t, e = visitor#visit_term () t in
    (Term t, e)
  | Binder s -> (Binder s, SMap.singleton s (UF.make st None))

let of_unifiable (f, _) = f

let subst_uvars st (f, e) : uterm =
  let visitor =
    object (self)
      inherit [_] map_spec as super

      (* most of the work is done in these encoded-variable cases *)

      method! visit_HigherOrder () f v =
        match v with
        | [] ->
          let f1 = super#visit_HigherOrder () f v in
          if is_uvar_name f then
            UF.get st (SMap.find f e) |> Option.get |> uterm_to_staged
          else f1
        | _ :: _ ->
          let f1 = super#visit_HigherOrder () f v in
          if is_uvar_name f then
            match UF.get st (SMap.find f e) |> Option.get |> uterm_to_term with
            | Var f2 ->
              (match f1 with
              | HigherOrder (_, v1) -> HigherOrder (f2, v1)
              | _ -> failwith "unreachable")
            | _ -> failwith "not a var"
          else f1

      method! visit_Predicate () f v =
        let p = super#visit_Predicate () f v in
        if is_uvar_name f then
          UF.get st (SMap.find f e) |> Option.get |> uterm_to_pure
        else p

      method! visit_PointsTo () l v =
        let p = super#visit_PointsTo () l v in
        if is_uvar_name l then
          UF.get st (SMap.find l e) |> Option.get |> uterm_to_heap
        else p

      method! visit_Var () x =
        if is_uvar_name x then
          UF.get st (SMap.find x e) |> Option.get |> uterm_to_term
        else Var x

      (* the remaining cases also handle capture-avoidance in addition to binder variables *)

      method! visit_Exists () x f =
        let x =
          if is_uvar_name x then
            UF.get st (SMap.find x e) |> Option.get |> uterm_to_binder
          else x
        in
        (* avoid capture *)
        let f1 = self#visit_staged_spec () f in
        let x2, f2 =
          let free = Subst.free_vars f1 in
          if SSet.mem x free then
            let y = Variables.fresh_variable ~v:x () in
            (* note the use of f, not f1 *)
            let f2 = f |> Subst.subst_free_vars [(x, Var y)] in
            let f2 = self#visit_staged_spec () f2 in
            (y, f2)
          else (x, f1)
        in
        Exists (x2, f2)

      (* other cases are copy-pasted *)

      method! visit_ForAll () x f =
        let x =
          if is_uvar_name x then
            UF.get st (SMap.find x e) |> Option.get |> uterm_to_binder
          else x
        in
        let f1 = self#visit_staged_spec () f in
        let x2, f2 =
          let free = Subst.free_vars f1 in
          if SSet.mem x free then
            let y = Variables.fresh_variable ~v:x () in
            let f2 = f |> Subst.subst_free_vars [(x, Var y)] in
            let f2 = self#visit_staged_spec () f2 in
            (y, f2)
          else (x, f1)
        in
        ForAll (x2, f2)

      method! visit_Bind () x f1 f2 =
        let x, f1, f2 =
          if is_uvar_name x then
            let b =
              UF.get st (SMap.find x e) |> Option.get |> uterm_to_binder
            in
            ( b,
              Subst.subst_free_vars [(x, Var b)] f1,
              Subst.subst_free_vars [(x, Var b)] f2 )
          else (x, f1, f2)
        in
        let f1 = self#visit_staged_spec () f1 in
        let f3 = self#visit_staged_spec () f2 in
        let x2, f2 =
          let free = Subst.free_vars f3 in
          if SSet.mem x free then
            let y = Variables.fresh_variable ~v:x () in
            (* note the use of f2, not f3 *)
            let f2 = f2 |> Subst.subst_free_vars [(x, Var y)] in
            let f2 = self#visit_staged_spec () f2 in
            (y, f2)
          else (x, f3)
        in
        Bind (x2, f1, f2)

      (* TODO other binders *)
    end
  in
  match f with
  | Staged s ->
    let s = visitor#visit_staged_spec () s in
    Staged s
  | Pure p ->
    let p = visitor#visit_pi () p in
    Pure p
  | Heap h ->
    let h = visitor#visit_kappa () h in
    Heap h
  | Term t ->
    let t = visitor#visit_term () t in
    Term t
  | Binder x ->
    if is_uvar_name x then UF.get st (SMap.find x e) |> Option.get else Binder x

let%expect_test "capture-avoidance" =
  Variables.reset_counter 0;
  let open Syntax in
  let st = UF.new_store () in
  let v = UF.make st (Some (Staged (ens ~p:(eq (v "x") (num 1)) ()))) in
  (* v has x free. sub it into a term which binds x. the binder needs to be renamed *)
  let ut =
    subst_uvars st
      (Staged (Exists ("x", HigherOrder ("__a", []))), SMap.singleton "__a" v)
  in
  Format.printf "%s@." (string_of_uterm ut);
  [%expect {| ex x0. (ens x=1) |}]

let string_of_outcome r = match r with None -> "fail" | Some _ -> "ok"

(* variables at the top level are handled in here. otherwise it delegates to the others *)
let rec unify_var : UF.store -> unifiable -> unifiable -> unit option =
 fun st (t1, e1) (t2, e2) ->
  let@ _ =
    span (fun r ->
        debug ~at:99 ~title:"unify_var" "%s ~ %s? %s" (string_of_uterm t1)
          (string_of_uterm t2)
          (string_of_result string_of_outcome r))
  in
  match (get_uvar t1, get_uvar t2) with
  | Some x1, Some x2 ->
    let u1 = SMap.find x1 e1 in
    let u2 = SMap.find x2 e2 in
    (match (UF.get st u1, UF.get st u2) with
    | None, None ->
      UF.union st u1 u2;
      Some ()
    | Some a, None ->
      UF.set st u2 (Some a);
      Some ()
    | None, Some a ->
      UF.set st u1 (Some a);
      Some ()
    | Some a1, Some a2 -> unify_var st (a1, e1) (a2, e2))
  | None, Some x2 ->
    let u2 = SMap.find x2 e2 in
    (match UF.get st u2 with
    | None ->
      UF.set st u2 (Some t1);
      Some ()
    | Some v2 -> unify_var st (t1, e1) (v2, e2))
  | Some x1, None ->
    let u1 = SMap.find x1 e1 in
    (match UF.get st u1 with
    | None ->
      UF.set st u1 (Some t2);
      Some ()
    | Some v1 -> unify_var st (v1, e1) (t2, e2))
  | None, None ->
    (* the two structures aren't variables at this level,
      so traverse them and call back in here at the next level *)
    (match (t1, t2) with
    | Staged s1, Staged s2 -> unify_staged st (s1, e1) (s2, e2)
    | Pure p1, Pure p2 -> unify_pure st (p1, e1) (p2, e2)
    | Heap h1, Heap h2 -> unify_heap st (h1, e1) (h2, e2)
    | Term t1, Term t2 -> unify_term st (t1, e1) (t2, e2)
    | Binder s1, Binder s2 when s1 = s2 -> Some ()
    | _, _ ->
      failwith
        (Format.sprintf "cannot unify values of different types: %s, %s"
           (string_of_uterm t1) (string_of_uterm t2)))

and unify_pure : UF.store -> pi unif -> pi unif -> unit option =
 fun st (p1, e1) (p2, e2) ->
  match (p1, p2) with
  | True, True | False, False -> Some ()
  | Imply (p1, p2), Imply (p3, p4)
  | Or (p1, p2), Or (p3, p4)
  | And (p1, p2), And (p3, p4) ->
    let* _ = unify_var st (Pure p1, e1) (Pure p3, e2) in
    let* _ = unify_var st (Pure p2, e1) (Pure p4, e2) in
    Some ()
  | Not p1, Not p2 ->
    let* _ = unify_var st (Pure p1, e1) (Pure p2, e2) in
    Some ()
  | Atomic (o1, t1, t2), Atomic (o2, t3, t4) when o1 = o2 ->
    let* _ = unify_var st (Term t1, e1) (Term t3, e2) in
    let* _ = unify_var st (Term t2, e1) (Term t4, e2) in
    Some ()
  | Predicate (f1, a1), Predicate (f2, a2) when f1 = f2 ->
    if List.length a1 <> List.length a2 then None
    else
      let* _ =
        sequence2
          (fun (v1, v2) -> unify_var st (Term v1, e1) (Term v2, e2))
          a1 a2
      in
      Some ()
  | Subsumption (t1, t2), Subsumption (t3, t4) ->
    let* _ = unify_var st (Term t1, e1) (Term t3, e2) in
    let* _ = unify_var st (Term t2, e1) (Term t4, e2) in
    Some ()
  | _, _ -> None

and unify_heap : UF.store -> kappa unif -> kappa unif -> unit option =
 fun st (p1, e1) (p2, e2) ->
  match (p1, p2) with
  | EmptyHeap, EmptyHeap -> Some ()
  | PointsTo (x1, v1), PointsTo (x2, v2) when x1 = x2 ->
    let* _ = unify_var st (Term v1, e1) (Term v2, e2) in
    Some ()
  | SepConj (h1, h2), SepConj (h3, h4) ->
    let* _ = unify_var st (Heap h1, e1) (Heap h3, e2) in
    let* _ = unify_var st (Heap h2, e1) (Heap h4, e2) in
    Some ()
  | _, _ -> None

and unify_term : UF.store -> term unif -> term unif -> unit option =
 fun st (t1, e1) (t2, e2) ->
  match (t1, t2) with
  | Const c1, Const c2 when c1 = c2 -> Some ()
  | Var x1, Var x2 when x1 = x2 -> Some ()
  | Rel (o1, t1, t2), Rel (o2, t3, t4) when o1 = o2 ->
    let* _ = unify_var st (Term t1, e1) (Term t3, e2) in
    let* _ = unify_var st (Term t2, e1) (Term t4, e2) in
    Some ()
  | BinOp (o1, t1, t2), BinOp (o2, t3, t4) when o1 = o2 ->
    let* _ = unify_var st (Term t1, e1) (Term t3, e2) in
    let* _ = unify_var st (Term t2, e1) (Term t4, e2) in
    Some ()
  | TNot t1, TNot t2 ->
    let* _ = unify_var st (Term t1, e1) (Term t2, e2) in
    Some ()
  | TApp (f1, a1), TApp (f2, a2) when f1 = f2 ->
    if List.length a1 <> List.length a2 then None
    else
      let* _ =
        sequence2
          (fun (v1, v2) -> unify_var st (Term v1, e1) (Term v2, e2))
          a1 a2
      in
      Some ()
  | TLambda (h1, ps1, sp1, b1), TLambda (h2, ps2, sp2, b2)
    when h1 = h2 && ps1 = ps2 && b1 = b2 ->
    (match (sp1, sp2) with
    | None, None -> Some ()
    | Some sp1, Some sp2 ->
      let* _ = unify_var st (Staged sp1, e1) (Staged sp2, e2) in
      Some ()
    | _, _ -> None)
  | TTuple _, TTuple _ -> failwith "TTuple"
  | _, _ -> None

and unify_staged :
    UF.store -> staged_spec unif -> staged_spec unif -> unit option =
 fun st (t1, e1) (t2, e2) ->
  match (t1, t2) with
  | Require (p1, h1), Require (p2, h2)
  | NormalReturn (p1, h1), NormalReturn (p2, h2) ->
    let* _ = unify_var st (Pure p1, e1) (Pure p2, e2) in
    let* _ = unify_var st (Heap h1, e1) (Heap h2, e2) in
    Some ()
  | Sequence (f1, f2), Sequence (f3, f4) ->
    let* _ = unify_var st (Staged f1, e1) (Staged f3, e2) in
    let* _ = unify_var st (Staged f2, e1) (Staged f4, e2) in
    Some ()
  | Exists (x1, b1), Exists (x2, b2) ->
    let* _ = unify_var st (Binder x1, e1) (Binder x2, e2) in
    let* _ = unify_var st (Staged b1, e1) (Staged b2, e2) in
    Some ()
  | ForAll (x1, b1), ForAll (x2, b2) ->
    let* _ = unify_var st (Binder x1, e1) (Binder x2, e2) in
    let* _ = unify_var st (Staged b1, e1) (Staged b2, e2) in
    Some ()
  | HigherOrder (f1, a1), HigherOrder (f2, a2) when f1 = f2 ->
    if List.length a1 <> List.length a2 then None
    else
      let* _ =
        sequence2
          (fun (v1, v2) -> unify_var st (Term v1, e1) (Term v2, e2))
          a1 a2
      in
      Some ()
  | Shift (z1, k1, f1), Shift (z2, k2, f2) when z1 = z2 && k1 = k2 ->
    let* _ = unify_var st (Staged f1, e1) (Staged f2, e2) in
    Some ()
  | Reset b1, Reset b2 ->
    let* _ = unify_var st (Staged b1, e1) (Staged b2, e2) in
    Some ()
  | Bind (x1, f1, f2), Bind (x2, f3, f4) ->
    let* _ = unify_var st (Binder x1, e1) (Binder x2, e2) in
    let* _ = unify_var st (Staged f1, e1) (Staged f3, e2) in
    let* _ = unify_var st (Staged f2, e1) (Staged f4, e2) in
    Some ()
  | Disjunction (f1, f2), Disjunction (f3, f4) ->
    let* _ = unify_var st (Staged f1, e1) (Staged f3, e2) in
    let* _ = unify_var st (Staged f2, e1) (Staged f4, e2) in
    Some ()
  | RaisingEff _, RaisingEff _ -> failwith "unimplemented RaisingEff"
  | TryCatch _, TryCatch _ -> failwith "unimplemented TryCatch"
  | _, _ -> None

let unify store t1 t2 =
  (* copy here to avoid clobbering the old state, as unification may fail.
    the new state is only made visible if it succeeds *)
  let s = UF.copy store in
  let+ _ = unify_var s t1 t2 in
  s

type rule = {
  lhs : uterm;
  rhs : [ `Replace of uterm | `Dynamic of (string -> uterm) -> uterm ];
}

let string_of_rule r =
  let rhs =
    match r.rhs with
    | `Replace u -> string_of_uterm u
    | `Dynamic _ -> "<dynamic>"
  in
  Format.asprintf "%s ==> %s" (string_of_uterm r.lhs) rhs

let rewrite_well_typed lhs target =
  match (lhs, target) with
  | Staged _, Staged _ | Pure _, Pure _ -> true
  | Heap _, Heap _ | Term _, Term _ -> true
  | _, _ -> false

let rewrite_rooted rule target =
  let@ _ =
    span (fun r ->
        debug ~at:4 ~title:"rewrite_rooted" "rule: %s\ntarget: %s\n==>\n%s"
          (string_of_rule rule) (string_of_uterm target)
          (string_of_result (string_of_option string_of_uterm) r))
  in
  if rewrite_well_typed rule.lhs target then
    let st = UF.new_store () in
    let lhs1, e = to_unifiable st rule.lhs in
    let target = to_unifiable st target in
    let+ s = unify st (lhs1, e) target in
    let inst_rhs =
      match rule.rhs with
      | `Replace rhs -> subst_uvars s (rhs, e)
      | `Dynamic f ->
        let mapping x = UF.get s (SMap.find (var_prefix ^ x) e) |> Option.get in
        f mapping
    in
    inst_rhs
  else Some target

let rewrite_all rule target =
  let visitor =
    object (_self)
      inherit [_] map_spec as super

      method! visit_staged_spec () s =
        let s1 = super#visit_staged_spec () s in
        (let+ s2 = rewrite_rooted rule (Staged s1) in
         uterm_to_staged s2)
        |> Option.value ~default:s1

      method! visit_pi () s =
        let s1 = super#visit_pi () s in
        (let+ s2 = rewrite_rooted rule (Pure s1) in
         uterm_to_pure s2)
        |> Option.value ~default:s1

      method! visit_kappa () s =
        let s1 = super#visit_kappa () s in
        (let+ s2 = rewrite_rooted rule (Heap s1) in
         uterm_to_heap s2)
        |> Option.value ~default:s1

      method! visit_term () s =
        let s1 = super#visit_term () s in
        (let+ s2 = rewrite_rooted rule (Term s1) in
         uterm_to_term s2)
        |> Option.value ~default:s1
    end
  in
  let@ _ =
    span (fun r ->
        debug ~at:4 ~title:"rewrite_all" "rule: %s\ntarget: %s\n==>\n%s"
          (string_of_rule rule) (string_of_uterm target)
          (string_of_result string_of_uterm r))
  in
  match target with
  | Staged s -> Staged (visitor#visit_staged_spec () s)
  | Pure p -> Pure (visitor#visit_pi () p)
  | Heap h -> Heap (visitor#visit_kappa () h)
  | Term t -> Term (visitor#visit_term () t)
  | Binder _ ->
    (match rewrite_rooted rule target with None -> target | Some t -> t)

(* put this into some other places *)
module Rules = struct
  module Staged = struct
    let uvar = uvar_staged
    let rule lhs rhs = { lhs = Staged lhs; rhs = `Replace (Staged rhs) }

    let dynamic_rule lhs rhs =
      { lhs = Staged lhs; rhs = `Dynamic (fun sub -> Staged (rhs sub)) }

    let of_uterm = uterm_to_staged
  end

  module Pure = struct
    let uvar = uvar_pure
    let rule lhs rhs = { lhs = Pure lhs; rhs = `Replace (Pure rhs) }
    let of_uterm = uterm_to_pure
  end

  module Heap = struct
    let uvar = uvar_heap
    let rule lhs rhs = { lhs = Heap lhs; rhs = `Replace (Heap rhs) }
    let of_uterm = uterm_to_heap
  end

  module Term = struct
    let uvar = uvar_term
    let rule lhs rhs = { lhs = Term lhs; rhs = `Replace (Term rhs) }

    let dynamic_rule lhs rhs =
      { lhs = Term lhs; rhs = `Dynamic (fun sub -> Term (rhs sub)) }

    let of_uterm = uterm_to_term
  end

  module Binder = struct
    let uvar = uvar_binder
    let of_uterm = uterm_to_binder
  end
end

exception Unification_failure of string

let fail fmt = Format.kasprintf (fun s -> raise (Unification_failure s)) fmt

let%expect_test "unification and substitution" =
  let open Syntax in
  let open Rules in
  let test a b =
    let st = UF.new_store () in
    let a1 = to_unifiable st a in
    let b1 = to_unifiable st b in
    match unify st a1 b1 with
    | None ->
      Format.printf "failed to unify (%s) and (%s)@." (string_of_uterm a)
        (string_of_uterm b)
    | Some s ->
      let a = subst_uvars s a1 in
      Format.printf "%s@." (string_of_uterm a)
  in
  let open Staged in
  let a = Staged (seq [uvar "n"; ens ()]) in
  let b = Staged (seq [ens ~p:(And (True, False)) (); ens ()]) in
  test a b;
  [%expect {| ens T/\F; ens emp |}];

  let a = Staged (seq [uvar "n"; uvar "n"; ens ()]) in
  let b =
    Staged
      (seq
         [ens ~p:(And (True, False)) (); ens ~p:(And (True, False)) (); ens ()])
  in
  test a b;
  [%expect {| ens T/\F; ens T/\F; ens emp |}]

let%expect_test "rewriting" =
  let open Syntax in
  let open Rules in
  let test rule b =
    let b1 = rewrite_all rule b in
    Format.printf "rewrite %s@." (string_of_uterm b);
    Format.printf "with %s@." (string_of_rule rule);
    Format.printf "result: %s@." (string_of_uterm b1)
  in
  test
    Staged.(
      rule (seq [uvar "n"; ens ()]) (seq [uvar "n"; uvar "n"; ens ~p:False ()]))
    (Staged (seq [ens ~p:(Not True) (); ens ~p:(And (True, False)) (); ens ()]));
  [%expect
    {|
    rewrite ens not(T); ens T/\F; ens emp
    with __n(); ens emp ==> __n(); __n(); ens F
    result: ens not(T); ens T/\F; ens T/\F; ens F
    |}];

  test (Staged.rule (ens ()) (ens ~p:False ())) (Staged (seq [ens (); ens ()]));
  [%expect
    {|
    rewrite ens emp; ens emp
    with ens emp ==> ens F
    result: ens F; ens F
    |}];

  test (Pure.rule True False) (Staged (seq [ens (); ens ()]));
  [%expect
    {|
    rewrite ens emp; ens emp
    with T ==> F
    result: ens F; ens F
    |}];

  test
    (Heap.rule (PointsTo ("x", Const (Num 1))) (PointsTo ("x", Const (Num 2))))
    (Staged (seq [ens ~h:(PointsTo ("x", Const (Num 1))) (); ens ()]));
  [%expect
    {|
    rewrite ens x->1; ens emp
    with x->1 ==> x->2
    result: ens x->2; ens emp
    |}];

  test
    (Term.rule (Const (Num 1)) (Const (Num 2)))
    (Staged (seq [ens ~h:(PointsTo ("x", Const (Num 1))) (); ens ()]));
  [%expect
    {|
    rewrite ens x->1; ens emp
    with 1 ==> 2
    result: ens x->2; ens emp
    |}];

  test
    Staged.(
      dynamic_rule
        (Bind
           (Binder.uvar "x", ens ~p:(eq (v "res") (Term.uvar "r")) (), uvar "f"))
        (fun sub ->
          let x = sub "x" |> Binder.of_uterm in
          let r = sub "r" |> Term.of_uterm in
          let f = sub "f" |> Staged.of_uterm in
          Subst.subst_free_vars [(x, r)] f))
    (Staged
       (seq
          [
            ens ();
            Bind
              ( "y",
                ens ~p:(eq (v "res") (Const (Num 1))) (),
                ens ~p:(eq (v "res") (Var "y")) () );
          ]));
  [%expect
    {|
    rewrite ens emp; let y = (ens res=1) in (ens res=y)
    with let __x = (ens res=__r) in (__f()) ==> <dynamic>
    result: ens emp; ens res=1
    |}];

  test
    (Staged.rule
       (HigherOrder ("f", [Term.uvar "x"]))
       (HigherOrder ("__x", [Const ValUnit])))
    (Staged (HigherOrder ("f", [Var "g"])));
  [%expect
    {|
    rewrite f(g)
    with f(__x) ==> __x(())
    result: g(())
    |}];

  (* binders *)
  let norm_bind_ex =
    Staged.rule
      (Bind
         ( Binder.uvar "x",
           Exists (Binder.uvar "x1", Staged.uvar "f"),
           Staged.uvar "fk" ))
      (Exists
         ( Binder.uvar "x1",
           Bind (Binder.uvar "x", Staged.uvar "f", Staged.uvar "fk") ))
  in
  test norm_bind_ex
    (Staged
       (Bind
          ( "x",
            Exists ("y", ens ~p:(eq (v "res") (v "y")) ()),
            ens ~p:(eq (v "x") (num 1)) () )));
  (* this is quite broken, so use dynamic rules for binders.
    the problem is the lack of contextual patterns relating binders to uses,
    so capture-avoidance doesn't work properly *)
  [%expect
    {|
    rewrite let x = (ex y. (ens res=y)) in (ens x=1)
    with let __x = (ex __x1. (__f())) in (__fk()) ==> ex __x1. (let __x = (__f()) in (__fk()))
    result: ex y2. (let x3 = (ens res=y) in (ens x=1))
    |}]

(* see tests.ml for more *)

type database = rule list

let string_of_database = string_of_list string_of_rule

let rec rewrite_until_no_change rule target =
  let target1 = rewrite_all rule target in
  (* TODO does the map visitor allow us to exploit ==? *)
  if target1 = target then target else rewrite_until_no_change rule target1

(** Rewrites until no more rules in the database apply *)
let rec autorewrite : database -> uterm -> uterm =
 fun db target ->
  let target1 =
    List.fold_left (fun t c -> rewrite_until_no_change c t) target db
  in
  (* TODO does the map visitor allow us to exploit ==? *)
  if target1 = target then target else autorewrite db target1

let norm_db =
  let open Syntax in
  let open Rules in
  Pure.
    [
      rule Term.(eq (uvar "a") (uvar "a")) True;
      rule (And (uvar "a", True)) (uvar "a");
      rule (And (True, uvar "a")) (uvar "a");
    ]
  @ Heap.
      [
        rule (SepConj (uvar "a", EmptyHeap)) (uvar "a");
        rule (SepConj (EmptyHeap, uvar "a")) (uvar "a");
      ]

let%expect_test "autorewrite" =
  let test db target =
    let b1 = autorewrite db target in
    Format.printf "start: %s@." (string_of_uterm target);
    Format.printf "result: %s@." (string_of_uterm b1)
  in
  let open Syntax in
  test norm_db
    (Staged (ens ~p:(conj [True; eq (v "x") (Const TTrue); True; True]) ()));
  [%expect {|
    start: ens T/\x=true/\T/\T
    result: ens x=true
    |}];

  test norm_db
    (Staged (ens ~p:(conj [True; eq (v "x") (v "x"); True; True]) ()));
  [%expect {|
    start: ens T/\x=x/\T/\T
    result: ens emp
    |}]

(** Named after the ppxlib module, which this is based on
    https://ocaml-ppx.github.io/ppxlib/ppxlib/matching-code.html
    https://github.com/ocaml-ppx/ppxlib/blob/main/src/ast_pattern0.ml
    https://github.com/ocaml-ppx/ppxlib/blob/main/src/ast_pattern.ml *)
module Ast_pattern = struct
  type ('matched_value, 'k, 'k_result) t =
    | T of ('matched_value -> 'k -> 'k_result)

  let __ = T (fun x k -> k x)
  let drop = T (fun _ k -> k)

  let as__ (T f1) =
    T
      (fun x k ->
        let k = f1 x (k x) in
        k)

  let const ?to_s v =
    T
      (fun x k ->
        if x = v then k
        else
          match to_s with
          | None -> fail "could not match constant"
          | Some to_s ->
            fail "could not match constant; expected %s but got %s" (to_s v)
              (to_s x))

  let true_ = const True

  let and_ (T pp1) (T pp2) =
    T
      (fun x k ->
        match x with
        | And (p1, p2) ->
          let k = pp1 p1 k in
          let k = pp2 p2 k in
          k
        | _ -> fail "could not match And; got %s" (string_of_pi x))

  let match_ (T p) u =
    let res = ref None in
    p u (fun a -> res := Some a);
    !res

  let%expect_test "unify" =
    let p1 = and_ true_ __ in
    let r = match_ p1 (And (True, True)) in
    Format.printf "%s@." (string_of_option string_of_pi r);
    [%expect {| Some T |}]

  let rewrite_rooted (T p) u k = p u k

  let%expect_test "rewrite" =
    let rule p k =
      let@ a = rewrite_rooted (and_ true_ __) p in
      k (And (a, True))
    in
    let r = Iter.head_exn (rule (And (True, False))) in
    Format.printf "%s@." (string_of_pi r);
    [%expect {| F/\T |}]

  let rewrite_all_pure lhs krhs =
    let visitor =
      object (_self)
        inherit [_] map_spec as super

        method! visit_pi () s =
          let s1 = super#visit_pi () s in
          try
            rewrite_rooted lhs s1 |> Iter.map krhs |> Iter.head
            |> Option.value ~default:s1
          with Unification_failure _ -> s1
      end
    in
    visitor

  let%expect_test "rewrite all" =
    let open Syntax in
    let target = ens ~p:(And (True, False)) () in
    let r =
      (rewrite_all_pure (and_ true_ __) (fun a -> And (a, True)))
        #visit_staged_spec () target
    in
    Format.printf "%s@." (string_of_staged_spec r);
    [%expect {| ens F/\T |}]
end

module Deep = struct
  type pattern =
    | Constr of string * pattern list
    | Inst of UF.t
    | Var of string

  let rec string_of_pattern p =
    match p with
    | Var s -> s
    | Inst _ -> "<inst>"
    | Constr (f, a) ->
      Format.asprintf "%s%s" f (string_of_args string_of_pattern a)

  let v s = Var s
  let and_ p1 p2 = Constr ("and", [p1; p2])
  let true_ = Constr ("true", [])

  let rec match_with st p u =
    match p with
    | Constr (f, a) ->
      (match (f, a, u) with
      | "true", [], Pure True -> ()
      | "and", [a1; a2], Pure (And (p1, p2)) ->
        match_with st a1 (Pure p1);
        match_with st a2 (Pure p2)
      | _, _, _ ->
        fail "unification failure: %s and %s" (string_of_pattern p)
          (string_of_uterm u))
    | Var _ -> failwith "invalid"
    | Inst x ->
      (match UF.get st x with
      | None -> UF.set st x (Some u)
      | Some u1 when u = u1 -> ()
      | Some u1 ->
        fail "unification failure: %s and %s" (string_of_uterm u)
          (string_of_uterm u1))

  let rec subst st p =
    match p with
    | Constr (f, a) ->
      (match (f, a) with
      | "true", [] -> Pure True
      | "and", [p1; p2] ->
        let p1 = subst st p1 |> uterm_to_pure in
        let p2 = subst st p2 |> uterm_to_pure in
        Pure (And (p1, p2))
      | _ -> failwith "unknown")
    | Var _ -> failwith "invalid"
    | Inst x -> UF.get st x |> Option.get

  let make_unifiable ?(e = SMap.empty) st p =
    let rec aux e p =
      match p with
      | Var s ->
        let e =
          SMap.update s
            (function None -> Some (UF.make st None) | Some v -> Some v)
            e
        in
        (Inst (SMap.find s e), e)
      | Inst _ -> (p, e)
      | Constr (f, a) ->
        let a, e =
          List.fold_right
            (fun c (cs, e) ->
              let c1, e = aux e c in
              (c1 :: cs, e))
            a ([], e)
        in
        (Constr (f, a), e)
    in
    aux e p

  let match_ p u =
    let st = UF.new_store () in
    let p, _ = make_unifiable st p in
    try
      match_with st p u;
      Some st
    with Failure _ -> None

  let rewrite_rooted lhs rhs u =
    let st = UF.new_store () in
    let lhs, e = make_unifiable st lhs in
    let rhs, _ = make_unifiable ~e st rhs in
    try
      match_with st lhs u;
      Some (subst st rhs)
    with Failure _ -> None

  let%expect_test "unify" =
    let p1 = and_ true_ (v "a") in
    let r = match_ p1 (Pure (And (True, True))) in
    Format.printf "%b@." (Option.is_some r);
    [%expect {| true |}]

  let%expect_test "rewrite" =
    let p1 = and_ true_ (v "a") in
    let p2 = and_ (v "a") true_ in
    let r = rewrite_rooted p1 p2 (Pure (And (True, False))) in
    Format.printf "%s@." (string_of_option string_of_uterm r);
    [%expect {| Some F/\T |}]
end
