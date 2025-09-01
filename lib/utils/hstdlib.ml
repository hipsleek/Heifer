(** Specific instances of Set and Map on strings. *)

(* the name is from Wstdlib in the Why3 api, i had no better ideas *)

module SSet = struct
  include Set.Make (String)

  let concat sets = List.fold_right union sets empty
  let to_list s = List.of_seq (to_seq s)
end

module SMap = struct
  include Map.Make (String)

  let keys m = bindings m |> List.map fst
  let values m = bindings m |> List.map snd

  let disjoint_or_fail k x y =
    match (x, y) with
    | Some v, None | None, Some v -> Some v
    | None, None -> None
    | Some v1, Some v2 when v1 == v2 || v1 = v2 -> Some v1
    | Some _, Some _ ->
      failwith (Format.asprintf "maps not disjoint on key %s" k)

  let merge_disjoint a b = merge disjoint_or_fail a b

  let merge_right_priority a b =
    merge (fun _k x y ->
      match x, y with
      | None, Some z | Some z, None -> Some z
      | None, None -> None
      | Some _, Some z -> Some z) a b

  let merge_arbitrary = merge_right_priority

  let intersect a b =
    merge (fun _ x y -> match x, y with
      | Some x, Some y when x = y -> Some x
      | _ -> None) a b

  let merge_all_disjoint xs =
    List.fold_right merge_disjoint xs empty

  let of_list xs = of_seq (List.to_seq xs)
end
