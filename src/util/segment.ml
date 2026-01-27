module Seg = struct
  (** Start inclusive, end exclusive. *)
  type t = int * int
  let length (p, q) = q - p
  let mem n (p, q) = p <= n && n < q
  let compare (p1, _) (p2, _) = Int.compare p1 p2
end

module SegSet = Set.Make(Seg)

module SegTree = struct
  (* non-overlapping segments *)
  type t = SegSet.t

  let empty = SegSet.empty

  let add n t =
    let find_min (_, q) = n < q in
    let find_max (_, q) = q <= n in
    match SegSet.find_first_opt find_min t with
    | None ->
        begin
          match SegSet.max_elt_opt t with
          | None -> SegSet.add (n, n + 1) t
          | Some (p, q as seg) ->
              if n = q
              then SegSet.add (p, n + 1) (SegSet.remove seg t)
              else SegSet.add (n, n + 1) t
        end
    | Some (pr, qr as segr) ->
        if pr <= n then t
        else
          match SegSet.find_last_opt find_max t with
          | None ->
              if n + 1 = pr
              then SegSet.add (n, qr) (SegSet.remove (pr, qr) t)
              else SegSet.add (n, n + 1) t
          | Some (pl, ql as segl) ->
              if n = ql && n + 1 = pr
              then SegSet.add (pl, qr) (SegSet.remove segl (SegSet.remove segr t))
              else if n = ql then SegSet.add (pl, n + 1) (SegSet.remove segl t)
              else if n + 1 = pr then SegSet.add (n, qr) (SegSet.remove segr t)
              else SegSet.add (n, n + 1) t

  let mem n t =
    let find (_, q) = n < q in
    match SegSet.find_first_opt find t with
    | None -> false
    | Some (p, _) -> p <= n

  let remove n t =
    let find (_, q) = n < q in
    match SegSet.find_first_opt find t with
    | None -> t
    | Some (p, q as seg) ->
        if p <= n then
          let t = SegSet.remove seg t in
          if p + 1 = q then t
          else if n = p then SegSet.add (n + 1, q) t
          else if n + 1 = q then SegSet.add (p, n) t
          else SegSet.add (p, n) (SegSet.add (n + 1, q) t)
        else t

  let length t = SegSet.fold (fun seg acc -> Seg.length seg + acc) t 0

  (** Inefficient, TODO: reimplement *)
  let rec add_seg (p, q) t =
    let t = add p t in
    if p + 1 = q then t else add_seg (p + 1, q) t

  let union t1 t2 =
    let t1, t2 =
      if length t1 <= length t2
      then t1, t2
      else t2, t1
    in
    SegSet.fold add_seg t1 t2

  let next n t =
    let find (_, q) = n < q in
    match SegSet.find_first_opt find t with
    | None -> n
    | Some (p, q) -> if p <= n then q else n

  (* let fresh i t = failwith "todo" *)

  let max_elt_opt t =
    match SegSet.max_elt_opt t with
    | None -> None
    | Some (_, q) -> Some (q - 1)
end
