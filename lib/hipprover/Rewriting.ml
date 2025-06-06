open Hipcore
open Hiptypes
open Pretty

let ( let* ) = Option.bind
let ( let+ ) a f = Option.map f a

(* currently there can only be variables at the staged_spec level *)
type uterm = staged_spec

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

(* unification (meta) variables are encoded in the AST with string names *)
let is_meta_var_name f = String.starts_with ~prefix:"_" f

let get_meta_var = function
  | HigherOrder (f, _) when is_meta_var_name f -> Some f
  | _ -> None

(* to avoid having a constructor for UF.t in the AST, use a layer of indirection *)
type unifiable = staged_spec * UF.t SMap.t

let to_unifiable st f : unifiable =
  let visitor =
    object (_)
      inherit [_] mapreduce_spec
      method zero = SMap.empty
      method plus = SMap.merge_arbitrary

      method! visit_HigherOrder () f v =
        if is_meta_var_name f then
          (HigherOrder (f, v), SMap.singleton f (UF.make st None))
        else (HigherOrder (f, v), SMap.empty)
    end
  in
  visitor#visit_staged_spec () f

let of_unifiable (f, _) = f

let subst_meta_vars st (f, e) : unifiable =
  let visitor =
    object (_)
      inherit [_] map_spec

      method! visit_HigherOrder () f v =
        if is_meta_var_name f then UF.get st (SMap.find f e) |> Option.get
        else HigherOrder (f, v)
    end
  in
  (visitor#visit_staged_spec () f, e)

let rec unify_aux : UF.store -> unifiable -> unifiable -> unit option =
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
  match (get_meta_var t1, get_meta_var t2) with
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
    | Some a1, Some a2 -> unify_aux st (a1, e1) (a2, e2))
  | None, Some x2 ->
    let u2 = SMap.find x2 e2 in
    (match UF.get st u2 with
    | None ->
      UF.set st u2 (Some t1);
      Some ()
    | Some v2 -> unify_aux st (t1, e1) (v2, e2))
  | Some x1, None ->
    let u1 = SMap.find x1 e1 in
    (match UF.get st u1 with
    | None ->
      UF.set st u1 (Some t2);
      Some ()
    | Some v1 -> unify_aux st (v1, e1) (t2, e2))
  | None, None ->
    (match (t1, t2) with
    | NormalReturn (p1, h1), NormalReturn (p2, h2) ->
      let* _ = unify_pure st p1 p2 in
      let* _ = unify_heap st h1 h2 in
      Some ()
    | Sequence (f1, f2), Sequence (f3, f4) ->
      let* _ = unify_aux st (f1, e1) (f3, e2) in
      let* _ = unify_aux st (f2, e1) (f4, e2) in
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
    | _, _ -> None)

and unify_pure : UF.store -> pi -> pi -> unit option =
 fun _st p1 p2 ->
  match (p1, p2) with
  | _, _ ->
    (* TODO no variables yet *)
    if p1 = p2 then Some () else None

and unify_heap : UF.store -> kappa -> kappa -> unit option =
 fun _st p1 p2 ->
  match (p1, p2) with
  | _, _ ->
    (* TODO no variables yet *)
    if p1 = p2 then Some () else None

let unify store t1 t2 =
  (* copy here to avoid clobbering the old state, as unification may fail.
    the new state is only made visible if it succeeds *)
  let s = UF.copy store in
  let+ _ = unify_aux s t1 t2 in
  s

type rule = {
  lhs : staged_spec;
  rhs : staged_spec;
}

let string_of_rule { lhs; rhs } =
  Format.asprintf "%s ==> %s"
    (string_of_staged_spec lhs)
    (string_of_staged_spec rhs)

let rewrite_rooted rule target =
  let st = UF.new_store () in
  let lhs, e = to_unifiable st rule.lhs in
  let target = to_unifiable st target in
  let+ s = unify st (lhs, e) target in
  let inst_rhs = subst_meta_vars s (rule.rhs, e) |> of_unifiable in
  inst_rhs

let rewrite_all rule target =
  let visitor =
    object (_self)
      inherit [_] map_spec as super

      method! visit_staged_spec () s =
        let s1 = super#visit_staged_spec () s in
        s1 |> rewrite_rooted rule |> Option.value ~default:s1
    end
  in
  visitor#visit_staged_spec () target

let mvar_spec n = HigherOrder ("_" ^ n, [])

let%expect_test "unification and substitution" =
  let test a b =
    let st = UF.new_store () in
    let a = to_unifiable st a in
    let b = to_unifiable st b in
    match unify st a b with
    | None -> Format.printf "failed@."
    | Some s ->
      let a = subst_meta_vars s a |> of_unifiable in
      Format.printf "%s@." (string_of_staged_spec a)
  in
  let a = Sequence (mvar_spec "n", NormalReturn (True, EmptyHeap)) in
  let b =
    Sequence
      ( NormalReturn (And (True, False), EmptyHeap),
        NormalReturn (True, EmptyHeap) )
  in
  test a b;
  [%expect {| ens T/\F; ens emp |}];

  let a =
    Sequence
      (mvar_spec "n", Sequence (mvar_spec "n", NormalReturn (True, EmptyHeap)))
  in
  let b =
    Sequence
      ( NormalReturn (And (True, False), EmptyHeap),
        Sequence
          ( NormalReturn (And (True, False), EmptyHeap),
            NormalReturn (True, EmptyHeap) ) )
  in
  test a b;
  [%expect {| ens T/\F; ens T/\F; ens emp |}]

let%expect_test "rewriting" =
  let rule =
    {
      lhs = Sequence (mvar_spec "n", NormalReturn (True, EmptyHeap));
      rhs =
        Sequence
          ( mvar_spec "n",
            Sequence (mvar_spec "n", NormalReturn (False, EmptyHeap)) );
    }
  in
  let b =
    Sequence
      ( NormalReturn (Not True, EmptyHeap),
        Sequence
          ( NormalReturn (And (True, False), EmptyHeap),
            NormalReturn (True, EmptyHeap) ) )
  in
  let b1 = rewrite_all rule b in
  Format.printf "rewrite %s@." (string_of_staged_spec b);
  Format.printf "with %s@." (string_of_rule rule);
  Format.printf "result: %s@." (string_of_staged_spec b1);
  [%expect
    {|
    rewrite ens not(T); ens T/\F; ens emp
    with _n(); ens emp ==> _n(); _n(); ens F
    result: ens not(T); ens T/\F; ens T/\F; ens F
    |}]
