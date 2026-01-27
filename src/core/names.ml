(* https://github.com/rocq-prover/rocq/blob/master/engine/nameops.ml *)

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
