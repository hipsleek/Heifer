open Hipcore
open Hiptypes
open Pretty

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

(* a string that we can lex, but not something likely to appear in programs or generated code *)
let var_prefix = "__"
let is_uvar_name f = String.starts_with ~prefix:var_prefix f
let uvar_staged n = HigherOrder (var_prefix ^ n, [])
let uvar_heap n = PointsTo (var_prefix ^ n, Const ValUnit)
let uvar_pure n = Predicate (var_prefix ^ n, [])
let uvar_term n = Var (var_prefix ^ n)

let get_uvar = function
  | Staged (HigherOrder (f, _)) when is_uvar_name f -> Some f
  | Pure (Predicate (f, _)) when is_uvar_name f -> Some f
  | Heap (PointsTo (f, _)) when is_uvar_name f -> Some f
  | Term (Var f) when is_uvar_name f -> Some f
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
  | Atomic (o1, t1, t2), Atomic (o2, t3, t4) when o1 = o2 ->
    let* _ = unify_var st (Term t1, e1) (Term t3, e2) in
    let* _ = unify_var st (Term t2, e1) (Term t4, e2) in
    Some ()
  | Predicate (f1, a1), Predicate (f2, a2) when f1 = f2 ->
    let* _ =
      sequence2 (fun (v1, v2) -> unify_var st (Term v1, e1) (Term v2, e2)) a1 a2
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
  | Rel (_, _, _), Rel (_, _, _) -> failwith "Rel"
  | BinOp (o1, t1, t2), BinOp (o2, t3, t4) when o1 = o2 ->
    let* _ = unify_var st (Term t1, e1) (Term t3, e2) in
    let* _ = unify_var st (Term t2, e1) (Term t4, e2) in
    Some ()
  | TNot t1, TNot t2 ->
    let* _ = unify_var st (Term t1, e1) (Term t2, e2) in
    Some ()
  | TApp (f1, a1), TApp (f2, a2) when f1 = f2 ->
    let* _ =
      sequence2 (fun (v1, v2) -> unify_var st (Term v1, e1) (Term v2, e2)) a1 a2
    in
    Some ()
  | TLambda (_, _, _, _), TLambda (_, _, _, _) -> failwith "TLambda"
  | TList _, TList _ -> failwith "TList"
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
  | Exists (x1, b1), Exists (x2, b2) when x1 = x2 ->
    (* TODO binders probably need to be handled as variables too... *)
    let* _ = unify_var st (Staged b1, e1) (Staged b2, e2) in
    Some ()
  | HigherOrder (f1, a1), HigherOrder (f2, a2) when f1 = f2 ->
    let* _ =
      sequence2 (fun (v1, v2) -> unify_var st (Term v1, e1) (Term v2, e2)) a1 a2
    in
    Some ()
  | Shift (z1, k1, f1), Shift (z2, k2, f2) when z1 = z2 && k1 = k2 ->
    let* _ = unify_var st (Staged f1, e1) (Staged f2, e2) in
    Some ()
  | Reset b1, Reset b2 ->
    let* _ = unify_var st (Staged b1, e1) (Staged b2, e2) in
    Some ()
  | Bind (x1, f1, f2), Bind (x2, f3, f4) when x1 = x2 ->
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

module Syntax = struct
  let seq fs = Utils.Lists.foldr1 (fun c t -> Sequence (c, t)) fs
  let ens ?(h = EmptyHeap) ?(p = True) () = NormalReturn (p, h)
  let conj fs = Utils.Lists.foldr1 (fun c t -> And (c, t)) fs
  let eq a b = Atomic (EQ, a, b)
  let ( = ) a b = eq a b
  let v a = Var a
end

module Rules = struct
  module Staged = struct
    let uvar = uvar_staged
    let rule lhs rhs = { lhs = Staged lhs; rhs = Staged rhs }
  end

  module Pure = struct
    let uvar = uvar_pure
    let rule lhs rhs = { lhs = Pure lhs; rhs = Pure rhs }
  end

  module Heap = struct
    let uvar = uvar_heap
    let rule lhs rhs = { lhs = Heap lhs; rhs = Heap rhs }
  end

  module Term = struct
    let uvar = uvar_term
    let rule lhs rhs = { lhs = Term lhs; rhs = Term rhs }
  end
end

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
    |}]
(* see tests.ml for more *)

type database = rule list

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
      rule (eq (Term.uvar "a") (Term.uvar "a")) True;
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
    (Staged (ens ~p:(conj [True; v "x" = Const TTrue; True; True]) ()));
  [%expect {|
    start: ens T/\x=true/\T/\T
    result: ens x=true
    |}];

  test norm_db (Staged (ens ~p:(conj [True; v "x" = v "x"; True; True]) ()));
  [%expect {|
    start: ens T/\x=true/\T/\T
    result: ens x=true
    |}]
