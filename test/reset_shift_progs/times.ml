let [@pure] rec times (xs : int list) : int =
  match xs with
  | [] -> 1
  | x :: xs' -> if x = 0 then 0 else x * times xs'

let rec times2_aux xs =
  match xs with
  | [] -> 1
  | x :: xs' -> if x = 0 then shift (fun k -> 0) else x * times2_aux xs'

[%%lemma{|
  times2_lemma(x, xs) =
    rs(let v75 = times2_aux(xs) in ens res = x *. v75) ==>
    ens res = x *. times(xs) |}]

let [@spec "ens res = times(xs)"] times2 xs =
  reset (times2_aux xs)
