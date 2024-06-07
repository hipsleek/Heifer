let ( let@ ) f x = f x

let rec replace_nth n y xs =
  match (n, xs) with
  | 0, [] -> []
  | 0, _ :: xs -> y :: xs
  | _, [] -> []
  | _, x :: xs1 -> x :: replace_nth (n - 1) y xs1

(** A write-only list that supports efficient accumulation from the back *)
module Acc : sig
  type 'a t

  val empty : 'a t
  val add : 'a -> 'a t -> 'a t
  val add_all : 'a list -> 'a t -> 'a t
  val to_list : 'a t -> 'a list
end = struct
  type 'a t = 'a list

  let empty = []
  let add = List.cons
  let add_all xs t = List.fold_left (Fun.flip List.cons) t xs
  let to_list = List.rev
end

let string_of_pair pa pb (a, b) = Format.asprintf "(%s, %s)" (pa a) (pb b)

let string_of_list p xs =
  match xs with
  | [] -> "[]"
  | _ ->
    let a = List.map p xs |> String.concat "; " in
    Format.asprintf "[%s]" a

let quote = Format.asprintf "\"%s\""

module SSet = struct
  include Set.Make (String)

  let concat sets = List.fold_right union sets empty
  let to_list s = List.of_seq (to_seq s)
end

module SMap = struct
  include Map.Make (String)

  let keys m = bindings m |> List.map fst

  let key_set m = bindings m |> List.map fst |> SSet.of_list

  let disjoint_or_fail k x y =
    match (x, y) with
    | Some v, None | None, Some v -> Some v
    | None, None -> None
    | Some v1, Some v2 when v1 == v2 || v1 = v2 -> Some v1
    | Some _, Some _ ->
      failwith (Format.asprintf "maps not disjoint on key %s" k)

  let merge_disjoint a b = merge disjoint_or_fail a b

  let merge_all_disjoint xs =
    List.fold_right merge_disjoint xs empty

  let of_list xs = of_seq (List.to_seq xs)
end

let rec unsnoc xs =
  match xs with
  | [] -> failwith "unsnoc"
  | [x] -> ([], x)
  | x :: xs ->
    let xs1, last = unsnoc xs in
    (x :: xs1, last)

let foldr1 f xs =
  match xs with
  | [] -> failwith "foldr1"
  | _ ->
    let xs, last = unsnoc xs in
    List.fold_right f xs last

let pair a b = (a, b)

let map_state env f xs =
  let r, env =
    List.fold_right (fun c (t, env) ->
      let r, e1 = f c env
      in (r :: t, e1)
    ) xs ([], env)
  in
  r, env

(** Like concat_map, but threads an extra "environment" argument through which can be updated by the function *)
let concat_map_state env f xs =
  let r, env = map_state env f xs in
  List.concat r, env

let%expect_test _ =
  let r, e = (concat_map_state 0 (fun x e -> [x; x * 3], e + 1) [1; 2; 3]) in
  Format.printf "%s %d@." (string_of_list string_of_int r) e;
  [%expect
    {| [1; 3; 2; 6; 3; 9] 3 |}]

let foldl1 f xs =
  match xs with
  | [] -> failwith "foldl1"
  | x :: xs1 ->
    List.fold_left f x xs1
