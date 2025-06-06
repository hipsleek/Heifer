open Hipcore
open Hiptypes
open Pretty

let ( let* ) = Option.bind
let ( let+ ) a f = Option.map f a

(* currently there can only be variables at the staged_spec level *)
type term = staged_spec

module UF : sig
  type t
  type store

  val new_store : unit -> store
  val copy : store -> store
  val make : store -> term option -> t
  val get : store -> t -> term option
  val set : store -> t -> term option -> unit
  val eq : store -> t -> t -> bool
  val union : store -> t -> t -> unit
end = struct
  module Store = UnionFind.StoreMap
  include UnionFind.Make (Store)

  type c = term option
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

(* to avoid having UF.t constructors in the AST, use a layer of indirection *)
type unifiable = staged_spec * UF.t SMap.t

let to_unifiable st f : unifiable =
  let visitor =
    object (_)
      inherit [_] mapreduce_spec
      method zero = SMap.empty
      method plus = SMap.merge_disjoint

      method! visit_HigherOrder _ f v =
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
    (* | HigherOrder _, HigherOrder _ -> failwith "todo" *)
    | _, _ -> failwith "unimplemented")

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

let%expect_test "hello world" =
  let a = Sequence (HigherOrder ("_f", []), NormalReturn (True, EmptyHeap)) in
  let b =
    Sequence
      ( NormalReturn (And (True, False), EmptyHeap),
        NormalReturn (True, EmptyHeap) )
  in
  let st = UF.new_store () in
  let a = to_unifiable st a in
  let b = to_unifiable st b in
  match unify st a b with
  | None -> Format.printf "failed@."
  | Some s ->
    let a = subst_meta_vars s a |> of_unifiable in
    Format.printf "%s@." (string_of_staged_spec a);
    [%expect {| ens T/\F; ens emp |}]
