let rec nat_identity n
(* req n >= 0 *)
= if n = 0 then 0 else 1 + nat_identity (n - 1)

(*@
  lemma nat_identity_summary n res =
    nat_identity(n, res) ==> ens res = n
@*)

let add_one n
(*@ ens res = n + 1 @*)
= nat_identity n + 1

let zero n
(*@ ens res = 0 @*)
= nat_identity n - n

let double n
(*@ ens res = n + n @*)
= nat_identity n + nat_identity n

let rec double_rec n
= if n = 0 then 0 else 2 + double_rec (n - 1)

(*@
  lemma double_rec n res =
    double_rec(n, res) ==> ens res = n + n
@*)

let zero_v1 n
(*@ ens res = 0 @*)
= double_rec n - n - n

let zero_v2 n
(*@ ens res = 0 @*)
= double_rec n - nat_identity n - n

let zero_v3 n
(*@ ens res = 0 @*)
= double_rec n - nat_identity n - nat_identity n

let zero_v4 n
(*@ ens res = 0 @*)
= double_rec n - double n


