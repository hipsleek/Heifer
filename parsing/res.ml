open Pretty

module Res = struct
  let ( let* ) = Result.bind

  (* type 'a pf = proof * 'a option *)

  (** A proof tree or counterexample produced during search.
      Disjunction is not shown explicitly, so only successful disjuncts appear.
      If the proof fails, represents a counterexample, which shows one path to the failure. *)
  type 'a pf = (proof * 'a, proof) result

  let all :
      ?may_elide:bool ->
      name:string ->
      to_s:('a -> string) ->
      'a list ->
      ('a -> 'b pf) ->
      'b list pf =
   fun ?(may_elide = false) ~name ~to_s vs f ->
    let rec loop pfs rs vs =
      match vs with
      (* special case, just inline the rule *)
      | [] -> Ok (rule ~children:(List.rev pfs) ~name "", rs)
      | [x] when may_elide -> f x |> Result.map (fun (p, a) -> (p, [a]))
      | x :: xs ->
        let res = f x in
        (match res with
        | Error p ->
          Error (rule ~children:(List.rev (p :: pfs)) ~name "%s" (to_s x))
        | Ok (p, r) -> loop (p :: pfs) (r :: rs) xs)
    in
    loop [] [] vs

  let any :
      ?may_elide:bool ->
      name:string ->
      to_s:('a -> string) ->
      'a list ->
      ('a -> 'b pf) ->
      'b pf =
   fun ?(may_elide = false) ~name ~to_s vs f ->
    match vs with
    | [] ->
      (* Error (rule ~name "choice empty") *)
      failwith (Format.asprintf "choice empty: %s" name)
    | [x] when may_elide -> f x (* special case, just inline *)
    | v :: vs ->
      (* return the first non-failing result, or the last failure if all fail *)
      let rec loop v vs =
        let res = f v in
        match (res, vs) with
        | Ok (p, r), _ -> Ok (rule ~name ~children:[p] "%s" (to_s v), r)
        | Error p, [] -> Error (rule ~name ~children:[p] "%s" (to_s v))
        | Error _, v1 :: vs1 -> loop v1 vs1
      in
      loop v vs
end

module Option = struct
  let ( let* ) = Option.bind
  let ( let+ ) a f = Option.map f a
  let succeeded = Option.is_some
  let ok = Some ()
  let fail = None
  let check b = if b then ok else fail
  let or_else o k = match o with None -> k () | Some _ -> o
  let of_bool default b = if b then Some default else None
  let pure a = Some a

  let all_ :
      to_s:('a -> string) -> 'a list -> ('a -> 'b option) -> 'b list option =
   fun ~to_s vs f ->
    let rec loop rs vs =
      match vs with
      | [] -> Some []
      | x :: xs ->
        info "%s %s@." (Pretty.yellow "(all)") (to_s x);
        let res = f x in
        (match res with None -> None | Some r -> loop (r :: rs) xs)
    in
    match vs with
    (* special case *)
    | [x] -> f x |> Option.map (fun y -> [y])
    | _ -> loop [] vs

  let all : to_s:('a -> string) -> 'a list -> ('a -> 'b option) -> unit option =
   fun ~to_s vs f -> all_ ~to_s vs f |> Option.map (fun _ -> ())

  let any :
      name:string ->
      to_s:('a -> string) ->
      'a list ->
      ('a -> 'b option) ->
      'b option =
   fun ~name ~to_s vs f ->
    match vs with
    | [] ->
      (* Error (rule ~name "choice empty") *)
      failwith (Format.asprintf "choice empty: %s" name)
      (* special case *)
    | [x] -> f x
    | v :: vs ->
      let rec loop v vs =
        info "%s %s@." (Pretty.yellow "(any)") (to_s v);
        let res = f v in
        match (res, vs) with
        | Some r, _ -> Some r
        | None, [] -> None
        | None, v1 :: vs1 -> loop v1 vs1
      in
      loop v vs

  let ensure cond = if cond then ok else fail

  let either :
      name:string ->
      (* to_s:(bool -> string) -> *)
      (bool -> 'b option) ->
      'b option =
   fun ~name f -> any ~name ~to_s:string_of_bool [true; false] f
end
