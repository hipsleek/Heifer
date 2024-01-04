
(* https://github.com/FabianWolff/closure-examples/blob/master/all.rs *)

let rec all xs pred
= match xs with
| [] -> true
| x :: xs' -> pred x && all xs' pred

let test1 xs (* FIXME *)
(*@ req xs->[1;2;3;4]; ens res=false @*)
= let is_equal_four v = v = 4 in
  all !xs is_equal_four

let test2 xs (* FIXME *)
(*@ req xs->[1;2;3;4]; ens res=true @*)
= let is_less_than_five v = v < 5 in
  all !xs is_less_than_five

let test3 xs (* FIXME *)
(*@ req xs->[1;2;3;4]; ens res=false @*)
= let is_less_than_three v = v < 3 in
  all !xs is_less_than_three
