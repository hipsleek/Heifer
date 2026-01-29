module Core = struct
  (** Start inclusive, end exclusive. *)
  type t = int * int
  let length (p, q) = q - p
  let mem n (p, q) = p <= n && n < q
  let compare (p1, _) (p2, _) = Int.compare p1 p2
end

module Set = Set.Make(Core)

module Tree = struct
  (* non-overlapping segments *)
  type t = Set.t

  let empty = Set.empty

  let add n t =
    let find_min (_, q) = n < q in
    let find_max (_, q) = q <= n in
    match Set.find_first_opt find_min t with
    | None ->
        begin
          match Set.max_elt_opt t with
          | None -> Set.add (n, n + 1) t
          | Some (p, q as seg) ->
              if n = q
              then Set.add (p, n + 1) (Set.remove seg t)
              else Set.add (n, n + 1) t
        end
    | Some (pr, qr as sr) ->
        if pr <= n then t
        else
          match Set.find_last_opt find_max t with
          | None ->
              if n + 1 = pr
              then Set.add (n, qr) (Set.remove sr t)
              else Set.add (n, n + 1) t
          | Some (pl, ql as sl) ->
              if n = ql && n + 1 = pr
              then Set.add (pl, qr) (Set.remove sl (Set.remove sr t))
              else if n = ql then Set.add (pl, n + 1) (Set.remove sl t)
              else if n + 1 = pr then Set.add (n, qr) (Set.remove sr t)
              else Set.add (n, n + 1) t

  let mem n t =
    let find (_, q) = n < q in
    match Set.find_first_opt find t with
    | None -> false
    | Some (p, _) -> p <= n

  let remove n t =
    let find (_, q) = n < q in
    match Set.find_first_opt find t with
    | None -> t
    | Some (p, q as s) ->
        if p <= n then
          let t = Set.remove s t in
          if p + 1 = q then t
          else if n = p then Set.add (n + 1, q) t
          else if n + 1 = q then Set.add (p, n) t
          else Set.add (p, n) (Set.add (n + 1, q) t)
        else t

  let length t = Set.fold (fun s acc -> Core.length s + acc) t 0

  (** Inefficient, TODO: reimplement *)
  let rec add_segment (p, q) t =
    let t = add p t in
    if p + 1 = q then t else add_segment (p + 1, q) t

  let union t1 t2 =
    let t1, t2 =
      if length t1 <= length t2
      then t1, t2
      else t2, t1
    in
    Set.fold add_segment t1 t2

  let next n t =
    let find (_, q) = n < q in
    match Set.find_first_opt find t with
    | None -> n
    | Some (p, q) -> if p <= n then q else n

  (* TODO: adopt efficient version *)
  let fresh n t =
    let o = next n t in
    o, add o t

  let max_elt_opt t =
    match Set.max_elt_opt t with
    | None -> None
    | Some (_, q) -> Some (q - 1)
end
