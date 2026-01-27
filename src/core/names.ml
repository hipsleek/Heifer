(* https://github.com/rocq-prover/rocq/blob/master/engine/nameops.ml *)

open Util

module Subscript = struct
  type t = {
    ss_zero : int;  (** Number of leading zeros of the subscript *)
    ss_subs : int;  (** Digital value of the subscript, zero meaning empty *)
  }

  let rec overflow n = n mod 10 = 9 && (n / 10 = 0 || overflow (n / 10))
  let zero = { ss_subs = 0; ss_zero = 0 }

  let succ s =
    if s.ss_subs = 0 then
      if s.ss_zero = 0 then
        (* [] -> [0] *)
        { ss_zero = 1; ss_subs = 0 }
      else
        (* [0...00] -> [0..01] *)
        { ss_zero = s.ss_zero - 1; ss_subs = 1 }
    else if overflow s.ss_subs then
      if s.ss_zero = 0 then
        (* [9...9] -> [10...0] *)
        { ss_zero = 0; ss_subs = 1 + s.ss_subs }
      else
        (* [0...009...9] -> [0...010...0] *)
        { ss_zero = s.ss_zero - 1; ss_subs = 1 + s.ss_subs }
    else
      (* [0...0n] -> [0...0{n+1}] *)
      { ss_zero = s.ss_zero; ss_subs = s.ss_subs + 1 }

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
