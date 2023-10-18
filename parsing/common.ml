let ( let@ ) f x = f x

let rec split_last xs =
  match xs with
  | [] -> failwith "split_last"
  | [x] -> ([], x)
  | x :: xs ->
    let init, last = split_last xs in
    (x :: init, last)

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
end

module SMap = struct
  include Map.Make (String)

  let keys m = bindings m |> List.map fst

  let merge_disjoint a b =
    merge
      (fun _k x y ->
        match (x, y) with
        | Some v, None | None, Some v -> Some v
        | None, None -> None
        | Some v1, Some v2 when v1 = v2 -> Some v1
        | Some _, Some _ ->
          failwith
            (Format.asprintf "maps with keys %s and %s should be disjoint"
               (string_of_list Fun.id (keys a))
               (string_of_list Fun.id (keys b))))
      a b
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