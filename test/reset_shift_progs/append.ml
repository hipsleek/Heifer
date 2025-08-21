let [@pure] rec append (xs : int list) (ys : int list) : int list =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys

let rec append_delim_aux xs =
  match xs with
  | [] -> shift (fun k -> k)
  | x :: xs' -> x :: append_delim_aux xs'

let rec append_cps xs ys k =
  match xs with
  | [] -> k ys
  | x :: xs' -> append_cps xs' ys (fun r -> k (x :: r))

(* unfold the body of append_delim here! *)

[%%lemma{|
  delim_to_cps(xs, ys) =
    let k = rs(append_delim_aux(xs)) in k(ys) ==>
    let k = (ens res = fun (r) -> (ens res = r)) in append_cps(xs, ys, k)
|}]

[%%lemma{|
  cps_to_direct(xs, ys, k) =
    append_cps(xs, ys, k) ==> let r = append(xs, ys) in k(r)
|}]

let [@spec "ens res = append(xs, ys)"] append_delim xs ys =
  (reset (append_delim_aux xs)) ys
