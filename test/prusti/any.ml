
(* https://github.com/FabianWolff/closure-examples/blob/master/any.rs *)

let rec any xs pred
= match xs with
| [] -> false
| x :: xs' -> pred x || any xs' pred

let rec integers n =
  if n <= 0 then []
  else n :: integers (n - 1)

let test1 n (* FIXME *)
(*@ req n>=3; ens res=true @*)
= let is_equal_three v = v = 3 in
  any (integers n) is_equal_three

let test2 n (* FIXME *)
(*@ req n<100; ens res=false @*)
= let is_equal_hundred v = v = 100 in
  any (integers n) is_equal_hundred

let test3 n (* FIXME *)
(*@ req n<10; ens res=false @*)
= let is_greater_than_ten v = v > 10 in
  any (integers n) is_greater_than_ten
