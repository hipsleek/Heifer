
(* https://github.com/FabianWolff/closure-examples/blob/master/any.rs *)

let rec any xs pred
= match xs with
| [] -> false
| x :: xs' -> pred x || any xs' pred

let test1 xs (* FIXME *)
(*@ req xs->[1;2;3]; ens res=true @*)
= let is_equal_three v = v = 3 in
  any !xs is_equal_three

let test2 xs (* FIXME *)
(*@ req xs->[1;2;3]; ens res=false @*)
= let is_equal_hundred v = v = 100 in
  any !xs is_equal_hundred

let test3 xs (* FIXME *)
(*@ req xs->[1;2;3]; ens res=false @*)
= let is_greater_than_ten v = v > 10 in
  any !xs is_greater_than_ten
