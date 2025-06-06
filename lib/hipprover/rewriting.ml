open Hipcore
open Hiptypes
open Pretty

let ( let* ) = Option.bind
let ( let+ ) a f = Option.map f a

(* currently there can only be variables at the staged_spec level *)
type uterm =
  | Staged of staged_spec
  | Pure of pi
  | Heap of kappa
  | Term of term

let string_of_uterm t =
  match t with
  | Staged s -> string_of_staged_spec s
  | Pure p -> string_of_pi p
  | Heap h -> string_of_kappa h
  | Term t -> string_of_term t

let uterm_to_staged = function Staged s -> s | _ -> failwith "not staged"
let uterm_to_pure = function Pure p -> p | _ -> failwith "not pure"
let uterm_to_heap = function Heap h -> h | _ -> failwith "not heap"
let uterm_to_term = function Term t -> t | _ -> failwith "not term"

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
let is_uvar_name f = String.starts_with ~prefix:"$" f

let get_uvar = function
  | Staged (HigherOrder (f, _)) when is_uvar_name f -> Some f
  | Pure (Predicate (f, _)) when is_uvar_name f -> Some f
  | _ -> None

(* to avoid having a constructor for UF.t in the AST, use a layer of indirection *)
type 'a unif = 'a * UF.t SMap.t
type unifiable = uterm unif

let to_unifiable st f : unifiable =
  let visitor =
    object (_)
      inherit [_] mapreduce_spec
      method zero = SMap.empty
      method plus = SMap.merge_arbitrary

      method! visit_HigherOrder () f v =
        if is_uvar_name f then
          (HigherOrder (f, v), SMap.singleton f (UF.make st None))
        else (HigherOrder (f, v), SMap.empty)

      method! visit_Predicate () f v =
        if is_uvar_name f then
          (Predicate (f, v), SMap.singleton f (UF.make st None))
        else (Predicate (f, v), SMap.empty)

      method! visit_PointsTo () l v =
        if is_uvar_name l then
          (PointsTo (l, v), SMap.singleton l (UF.make st None))
        else (PointsTo (l, v), SMap.empty)

      method! visit_Var () x =
        if is_uvar_name x then (Var x, SMap.singleton x (UF.make st None))
        else (Var x, SMap.empty)
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
    let p, e = visitor#visit_kappa () h in
    (Heap p, e)
  | Term t ->
    let p, e = visitor#visit_term () t in
    (Term p, e)

let of_unifiable (f, _) = f

let subst_uvars st (f, e) : uterm =
  let visitor =
    object (_)
      inherit [_] map_spec

      method! visit_HigherOrder () f v =
        if is_uvar_name f then
          UF.get st (SMap.find f e) |> Option.get |> uterm_to_staged
        else HigherOrder (f, v)

      method! visit_Predicate () f v =
        if is_uvar_name f then
          UF.get st (SMap.find f e) |> Option.get |> uterm_to_pure
        else Predicate (f, v)

      method! visit_PointsTo () l v =
        if is_uvar_name l then
          UF.get st (SMap.find l e) |> Option.get |> uterm_to_heap
        else PointsTo (l, v)

      method! visit_Var () x =
        if is_uvar_name x then
          UF.get st (SMap.find x e) |> Option.get |> uterm_to_term
        else Var x
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

(* variables at the top level are handled in here. otherwise it delegates to the others *)
let rec unify_var : UF.store -> unifiable -> unifiable -> unit option =
 fun st (t1, e1) (t2, e2) ->
  (* let@ _ =
    Debug.span (fun m r ->
        m
          ~title:(if matching then "unify-match" else "unify")
          "%a ~ %a? %a" pretty_term t1 pretty_term t2 (Fmt.res Fmt.string)
          (Option.map
             (fun r1 -> if Option.is_some r1 then "ok" else "failed")
             r))
  in *)
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
  | Atomic (_, _, _), Atomic (_, _, _) -> failwith "Atomic"
  | Predicate (_, _), Predicate (_, _) -> failwith "Predicate"
  | Subsumption (_, _), Subsumption (_, _) -> failwith "Subsumption"
  | _, _ -> None

and unify_heap : UF.store -> kappa unif -> kappa unif -> unit option =
 fun st (p1, e1) (p2, e2) ->
  match (p1, p2) with
  | EmptyHeap, EmptyHeap -> Some ()
  | PointsTo (_, _), PointsTo (_, _) -> failwith "points"
  | SepConj (_, _), SepConj (_, _) -> failwith "sepconj"
  | _, _ -> None

and unify_term : UF.store -> term unif -> term unif -> unit option =
 fun st (t1, e1) (t2, e2) ->
  match (t1, t2) with
  | Const _, Const _ -> failwith "Const"
  | Var _, Var _ -> failwith "Var"
  | Rel (_, _, _), Rel (_, _, _) -> failwith "Rel"
  | BinOp (_, _, _), BinOp (_, _, _) -> failwith "BinOp"
  | TNot _, TNot _ -> failwith "TNot"
  | TApp (_, _), TApp (_, _) -> failwith "TApp"
  | TLambda (_, _, _, _), TLambda (_, _, _, _) -> failwith "TLambda"
  | TList _, TList _ -> failwith "TList"
  | TTuple _, TTuple _ -> failwith "TTuple"
  | _, _ -> None

and unify_staged :
    UF.store -> staged_spec unif -> staged_spec unif -> unit option =
 fun st (t1, e1) (t2, e2) ->
  match (t1, t2) with
  | NormalReturn (p1, h1), NormalReturn (p2, h2) ->
    let* _ = unify_var st (Pure p1, e1) (Pure p2, e2) in
    let* _ = unify_var st (Heap h1, e1) (Heap h2, e2) in
    Some ()
  | Sequence (f1, f2), Sequence (f3, f4) ->
    let* _ = unify_var st (Staged f1, e1) (Staged f3, e2) in
    let* _ = unify_var st (Staged f2, e1) (Staged f4, e2) in
    Some ()
  | Exists (_, _), Exists (_, _) -> failwith "unimplemented Exists"
  | Require (_, _), Require (_, _) -> failwith "unimplemented Require"
  | HigherOrder (_, _), HigherOrder (_, _) ->
    failwith "unimplemented HigherOrder"
  | Shift (_, _, _), Shift (_, _, _) -> failwith "unimplemented Shift"
  | Reset _, Reset _ -> failwith "unimplemented Reset"
  | Bind (_, _, _), Bind (_, _, _) -> failwith "unimplemented Bind"
  | Disjunction (_, _), Disjunction (_, _) ->
    failwith "unimplemented Disjunction"
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
  rhs : uterm;
}

let string_of_rule { lhs; rhs } =
  Format.asprintf "%s ==> %s" (string_of_uterm lhs) (string_of_uterm rhs)

let rewrite_applicable rule target =
  match (rule.lhs, target) with
  | Staged _, Staged _ | Pure _, Pure _ -> true
  | Heap _, Heap _ | Term _, Term _ -> true
  | _, _ -> false

let rewrite_rooted rule target =
  if rewrite_applicable rule target then
    let st = UF.new_store () in
    let lhs, e = to_unifiable st rule.lhs in
    let target = to_unifiable st target in
    let+ s = unify st (lhs, e) target in
    let inst_rhs = subst_uvars s (rule.rhs, e) in
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
  match target with
  | Staged s -> Staged (visitor#visit_staged_spec () s)
  | Pure p -> Pure (visitor#visit_pi () p)
  | Heap h -> Heap (visitor#visit_kappa () h)
  | Term t -> Term (visitor#visit_term () t)

let uvar_spec n = HigherOrder ("$" ^ n, [])

let%expect_test "unification and substitution" =
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
  let a = Staged (Sequence (uvar_spec "n", NormalReturn (True, EmptyHeap))) in
  let b =
    Staged
      (Sequence
         ( NormalReturn (And (True, False), EmptyHeap),
           NormalReturn (True, EmptyHeap) ))
  in
  test a b;
  [%expect {| ens T/\F; ens emp |}];

  let a =
    Staged
      (Sequence
         ( uvar_spec "n",
           Sequence (uvar_spec "n", NormalReturn (True, EmptyHeap)) ))
  in
  let b =
    Staged
      (Sequence
         ( NormalReturn (And (True, False), EmptyHeap),
           Sequence
             ( NormalReturn (And (True, False), EmptyHeap),
               NormalReturn (True, EmptyHeap) ) ))
  in
  test a b;
  [%expect {| ens T/\F; ens T/\F; ens emp |}]

let%expect_test "rewriting" =
  let rule =
    {
      lhs = Staged (Sequence (uvar_spec "n", NormalReturn (True, EmptyHeap)));
      rhs =
        Staged
          (Sequence
             ( uvar_spec "n",
               Sequence (uvar_spec "n", NormalReturn (False, EmptyHeap)) ));
    }
  in
  let b =
    Staged
      (Sequence
         ( NormalReturn (Not True, EmptyHeap),
           Sequence
             ( NormalReturn (And (True, False), EmptyHeap),
               NormalReturn (True, EmptyHeap) ) ))
  in
  let b1 = rewrite_all rule b in
  Format.printf "rewrite %s@." (string_of_uterm b);
  Format.printf "with %s@." (string_of_rule rule);
  Format.printf "result: %s@." (string_of_uterm b1);
  [%expect
    {|
    rewrite ens not(T); ens T/\F; ens emp
    with $n(); ens emp ==> $n(); $n(); ens F
    result: ens not(T); ens T/\F; ens T/\F; ens F
    |}]

type database = rule list

(** Rewrites until no more rules in the database apply *)
let autorewrite : database -> uterm -> uterm =
 fun _db _target -> failwith "todo"
