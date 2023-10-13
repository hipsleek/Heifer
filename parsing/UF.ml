(* Union-find with path compression and linking by rank.
   Unlike https://gitlab.inria.fr/fpottier/unionfind, allows the representative of the equivalence class to be specified. *)
module Make (E : sig
  type t

  val eq : t -> t -> bool
  val choose : t -> t -> t
  val pp : Format.formatter -> t -> unit
end) : sig
  type t

  val elt : E.t -> t
  val find : t -> t
  val value : t -> E.t
  val pp : Format.formatter -> t -> unit
  val show : (Format.formatter -> 'a -> unit) -> 'a -> string
  val equal : t -> t -> bool

  val union : (* ?choose:(E.t -> E.t -> E.t) -> *)
              t -> t -> unit
end = struct
  type node =
    | Node of t
    | Root of {
        value : E.t;
        rank : int;
      }

  and t = node ref

  let elt v = ref (Root { value = v; rank = 0 })

  let rec find n =
    match !n with
    | Root _ -> n
    | Node p ->
      (* path compression *)
      let r = find p in
      if Stdlib.(r != p) then p := Node r;
      r

  let value n =
    match !(find n) with
    | Root { value = v; _ } -> v
    | _ -> failwith "must be a root"

  let pp fmt t = Format.fprintf fmt "%a" E.pp (value t)
  let show pp x = Format.asprintf "%a" pp x

  (* TODO should this call E.eq and not just check the physical equality of the ref? *)
  let equal n1 n2 = E.eq (n1 |> find |> value) (n2 |> find |> value)

  let rec union (* ?(choose = E.choose) *) n1 n2 =
    match (!n1, !n2) with
    | Root { value = v1; rank = r1 }, Root { value = v2; rank = r2 } ->
      let v3 = E.choose v1 v2 in
      let v3 =
        if E.eq v3 v1 then v1
        else if E.eq v3 v2 then v2
        else failwith "f should return one of its arguments"
      in
      (* linking by rank: the shorter subtree becomes the child *)
      (* because we ultimately link by rank, the value chosen doesn't matter unless there is a tie and we create a new root *)
      (match () with
      | _ when r1 < r2 -> n1 := Node n2 (* ; n2 *)
      | _ when r1 > r2 -> n2 := Node n1 (* ; n1 *)
      | _ ->
        n1 := Node n2;
        n2 := Root { value = v3; rank = r2 + 1 } (* ; n2 *))
    | _, _ -> union (find n1) (find n2)
end

module Int = Make (struct
  type t = int

  let choose = min
  let eq = Int.equal
  let pp = Format.pp_print_int
end)

module Str = Make (struct
  type t = string

  let choose a b = if String.compare a b <= 0 then a else b
  let eq = String.equal
  let pp = Format.pp_print_string
end)

let%expect_test "union find" =
  let b = Int.elt 1 in
  let a = Int.elt 2 in
  (* let c = Int.elt 3 in *)
  Format.printf "%d %d@." (Int.value a) (Int.value b);
  Int.union b a;
  Format.printf "%d %d@." (Int.value a) (Int.value b);
  (* Int.union ~choose:max a c; *)
  (* Format.printf "%d %d@." (Int.value a) (Int.value b); *)
  [%expect {|
    2 1
    1 1
|}]
