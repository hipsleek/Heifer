(* https://github.com/rocq-prover/rocq/blob/master/engine/nameops.ml *)

open Util

module Subscript = struct
  type t = {
    ss_zero : int;  (** Number of leading zeros of the subscript *)
    ss_subs : int;  (** Digital value of the subscript, zero meaning empty *)
  }

  let rec overflow n = n mod 10 = 9 && (n / 10 = 0 || overflow (n / 10))
  let zero = { ss_subs = 0; ss_zero = 0 }

  let succ { ss_zero; ss_subs } =
    if ss_subs = 0 then
      if ss_zero = 0 then
        (* [] -> [0] *)
        { ss_zero = 1; ss_subs = 0 }
      else
        (* [0...00] -> [0..01] *)
        { ss_zero = ss_zero - 1; ss_subs = 1 }
    else if overflow ss_subs then
      if ss_zero = 0 then
        (* [9...9] -> [10...0] *)
        { ss_zero = 0; ss_subs = 1 + ss_subs }
      else
        (* [0...009...9] -> [0...010...0] *)
        { ss_zero = ss_zero - 1; ss_subs = 1 + ss_subs }
    else
      (* [0...0n] -> [0...0{n+1}] *)
      { ss_zero; ss_subs = ss_subs + 1 }

  let equal s1 s2 = s1.ss_zero = s2.ss_zero && s1.ss_subs = s2.ss_subs

  let compare s1 s2 =
    (* Lexicographic order is reversed in order to ensure that [succ] is strictly
      increasing. *)
    let c = Int.compare s1.ss_subs s2.ss_subs in
    if c = 0 then Int.compare s1.ss_zero s2.ss_zero else c
end

let cut_ident skip_quote s =
  let len = String.length s in
  (* [n'] is the position of the first non nullary digit *)
  let rec numpart n n' =
    if n = 0 then
      (* ident made of _ and digits only [and ' if skip_quote]: don't cut it *)
      len
    else
      let c = s.[n - 1] in
      if c = '0' && n <> len then numpart (n - 1) n'
      else if Chars.is_digit c then numpart (n - 1) (n - 1)
      else if skip_quote && (c = '\'' || c = '_') then numpart (n - 1) (n - 1)
      else n'
  in
  numpart len len

let repr_ident s =
  let numstart = cut_ident false s in
  let len = String.length s in
  if numstart = len then (s, None)
  else (String.sub s 0 numstart, Some (int_of_string (String.sub s numstart (len - numstart))))

let make_ident s = function
  | None -> s
  | Some n ->
      let c = Strings.get_last s in
      let n = string_of_int n in
      if not (Chars.is_digit c) then s ^ n else s ^ "_" ^ n

let increment_subscript s =
  let len = String.length s in
  let rec add carrypos =
    let c = s.[carrypos] in
    if Chars.is_digit c then
      if c = '9' then begin
        assert (carrypos > 0);
        add (carrypos - 1)
      end
      else begin
        let newid = Bytes.of_string s in
        Bytes.fill newid (carrypos + 1) (len - carrypos - 1) '0';
        Bytes.set newid carrypos (Chars.succ c);
        newid
      end
    else begin
      let newid = Bytes.of_string (s ^ "0") in
      if carrypos < len - 1 then begin
        Bytes.fill newid (carrypos + 1) (len - carrypos - 1) '0';
        Bytes.set newid (carrypos + 1) '1'
      end;
      newid
    end
  in
  add (len - 1)

let has_subscript s = Chars.is_digit (Strings.get_last s)

let get_subscript s =
  let len = String.length s in
  let rec get_suf pos acc =
    if pos < 0 then (pos, acc)
    else
      let c = s.[pos] in
      if Chars.is_digit c then get_suf (pos - 1) ((Char.code c - Char.code '0') :: acc)
      else (pos, acc)
  in
  let pos, suf = get_suf (len - 1) [] in
  if pos = len - 1 then (s, Subscript.zero)
  else
    let s = String.sub s 0 (pos + 1) in
    let rec compute_zeros acc = function
      | [] -> (acc, [])
      | 0 :: suf -> compute_zeros (acc + 1) suf
      | suf -> (acc, suf)
    in
    let ss_zero, suf = compute_zeros 0 suf in
    let ss_subs = List.fold_left (fun acc n -> (10 * acc) + n) 0 suf in
    (s, { ss_subs; ss_zero })

let add_subscript s ss =
  if Subscript.equal Subscript.zero ss then s
  else if ss.Subscript.ss_subs = 0 then
    let pad = String.make ss.Subscript.ss_zero '0' in
    Printf.sprintf "%s%s" s pad
  else
    let pad = String.make ss.Subscript.ss_zero '0' in
    let suf = ss.Subscript.ss_subs in
    Printf.sprintf "%s%s%i" s pad suf

let forget_subscript s =
  let numstart = cut_ident false s in
  let newid = Bytes.make (numstart + 1) '0' in
  String.blit s 0 newid 0 numstart;
  String.of_bytes newid

(* THE CODE BELOW ARE PORTED AND COMPILE, BUT IT HAVEN'T BEEN CHECKED *)

module SubSet = struct
  type t = {
    num : Segment.Tree.t;
    pre : Segment.Tree.t list; (* lists are OK because we are already logarithmic *)
  }
  (* We represent sets of subscripts by case-splitting on ss_zero.
     If it is zero, we store the number in the [num] set. Otherwise, we know
     the set of possible values is finite. At position k, [pre] contains a set
     of maximum size 10^k representing k-digit numbers with at least one leading
     zero. *)

  let empty = { num = Segment.Tree.empty; pre = [] }
  let max_subscript Subscript.{ ss_zero; ss_subs } = Maths.pow10 (Maths.log10 ss_subs + ss_zero - 1)

  let add ss s =
    let open Subscript in
    if Int.equal ss.ss_zero 0 then { s with num = Segment.Tree.add ss.ss_subs s.num }
    else
      let pre =
        let len = List.length s.pre in
        if len < ss.ss_zero then s.pre @ Lists.make (ss.ss_zero - len) Segment.Tree.empty else s.pre
      in
      let set =
        match List.nth_opt pre (ss.ss_zero - 1) with
        | None -> assert false
        | Some m -> Segment.Tree.add ss.ss_subs m
      in
      { s with pre = Lists.set_nth (ss.ss_zero - 1) set pre }

  let union { num = num1; pre = pre1 } { num = num2; pre = pre2 } =
    let rec merge_pre pre1 pre2 =
      match (pre1, pre2) with
      | [], x | x, [] -> x
      | v1 :: rest1, v2 :: rest2 -> Segment.Tree.union v1 v2 :: merge_pre rest1 rest2
    in
    let num = Segment.Tree.union num1 num2 in
    { num; pre = merge_pre pre1 pre2 }

  let remove ss s =
    let open Subscript in
    if Int.equal ss.ss_zero 0 then { s with num = Segment.Tree.remove ss.ss_subs s.num }
    else
      match List.nth_opt s.pre (ss.ss_zero - 1) with
      | None -> s
      | Some m ->
          let m = Segment.Tree.remove ss.ss_subs m in
          { s with pre = Lists.set_nth (ss.ss_zero - 1) m s.pre }

  let mem ss s =
    let open Subscript in
    if Int.equal ss.ss_zero 0 then Segment.Tree.mem ss.ss_subs s.num
    else
      match List.nth_opt s.pre (ss.ss_zero - 1) with
      | None -> false
      | Some m -> Segment.Tree.mem ss.ss_subs m

  let ss_O = { Subscript.ss_zero = 1; ss_subs = 0 } (* [0] *)

  let next ss s =
    let open Subscript in
    if ss.ss_zero > 0 then
      match List.nth_opt s.pre (ss.ss_zero - 1) with
      | None -> ss
      | Some m ->
          let next = Segment.Tree.next ss.ss_subs m in
          let max = max_subscript ss in
          if max <= next then (* overflow *)
            { ss_zero = 0; ss_subs = Segment.Tree.next max s.num }
          else { ss_zero = ss.ss_zero; ss_subs = next }
    else if Int.equal ss.ss_subs 0 then
      (* Handle specially [] *)
      if not @@ Segment.Tree.mem 0 s.num then Subscript.zero
      else
        match s.pre with
        | [] -> ss_O
        | m :: _ ->
            if Segment.Tree.mem 0 m then { ss_zero = 0; ss_subs = Segment.Tree.next 1 s.num } else ss_O
    else { ss_zero = 0; ss_subs = Segment.Tree.next ss.ss_subs s.num }

  let fresh ss s =
    let open Subscript in
    if ss.ss_zero > 0 then
      match List.nth_opt s.pre (ss.ss_zero - 1) with
      | None -> (ss, add ss s)
      | Some m ->
          let subs, m = Segment.Tree.fresh ss.ss_subs m in
          let max = max_subscript ss in
          if max <= subs then
            let subs, num = Segment.Tree.fresh max s.num in
            ({ ss_zero = 0; ss_subs = subs }, { s with num })
          else
            let s = { s with pre = Lists.set_nth (ss.ss_zero - 1) m s.pre } in
            ({ ss_zero = ss.ss_zero; ss_subs = subs }, s)
    else if Int.equal ss.ss_subs 0 then
      if not @@ Segment.Tree.mem 0 s.num then (Subscript.zero, { num = Segment.Tree.add 0 s.num; pre = s.pre })
      else
        match s.pre with
        | [] -> (ss_O, { num = s.num; pre = [Segment.Tree.add 0 Segment.Tree.empty] })
        | m :: rem ->
            if Segment.Tree.mem 0 m then
              let subs, num = Segment.Tree.fresh 1 s.num in
              ({ ss_zero = 0; ss_subs = subs }, { num; pre = s.pre })
            else (ss_O, { num = s.num; pre = Segment.Tree.add 0 Segment.Tree.empty :: rem })
    else
      let subs, num = Segment.Tree.fresh ss.ss_subs s.num in
      ({ ss_zero = 0; ss_subs = subs }, { s with num })

  let max_elt_opt s =
    let mapi i m =
      match Segment.Tree.max_elt_opt m with
      | None -> None
      | Some k -> Some { Subscript.ss_zero = i; ss_subs = k }
    in
    let maxs = List.mapi mapi (s.num :: s.pre) in
    let fold s accu =
      match s with
      | None -> accu
      | Some ss ->
          (match accu with
          | None -> Some ss
          | Some ss' -> if Subscript.compare ss ss' <= 0 then accu else s)
    in
    List.fold_left fold None maxs
end

module Fresh = struct
  open Util.Strings

  type t = SubSet.t SMap.t

  let empty = SMap.empty

  let add id m =
    let id, s = get_subscript id in
    let old = try SMap.find id m with Not_found -> SubSet.empty in
    SMap.add id (SubSet.add s old) m

  let union m1 m2 = SMap.union (fun _ s1 s2 -> Some (SubSet.union s1 s2)) m1 m2

  let remove id m =
    let id, s = get_subscript id in
    match SMap.find id m with
    | old -> SMap.add id (SubSet.remove s old) m
    | exception Not_found -> m

  let mem id m =
    let id, s = get_subscript id in
    try SubSet.mem s (SMap.find id m) with Not_found -> false

  let next id0 m =
    let id, s = get_subscript id0 in
    match SMap.find_opt id m with
    | None -> id0
    | Some old ->
        let ss = SubSet.next s old in
        add_subscript id ss

  let fresh id0 m =
    let id, s = get_subscript id0 in
    match SMap.find_opt id m with
    | None -> (id0, SMap.add id (SubSet.add s SubSet.empty) m)
    | Some old ->
        let ss, n = SubSet.fresh s old in
        (add_subscript id ss, SMap.add id n m)

  let of_list l = List.fold_left (fun accu id -> add id accu) empty l
  let of_set s = SSet.fold add s empty

  let max_map s =
    let filter _ m = SubSet.max_elt_opt m in
    SMap.filter_map filter s
end
