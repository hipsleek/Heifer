
(* https://github.com/FabianWolff/closure-examples/blob/master/blameassgn.rs *)


(* Temporary workaround to specify preconditions on the function argument and result *)
let apply fn v
(*@ req v>9; ex r; fn(v, r); req r>=0/\r<=99 @*)
= fn v

let g_fail g = apply g 0 (* Gives a specification of `req false` *)
let g_ok g = apply g 10

let h v
(*@ req v>9; ens res>=50/\res<=99 @*)
= 66

(*
  Partial application is not yet supported, so `10` is used as a value to satisfy
  preconditions on the parameter of the function.
*)

let h_ok () = apply h 10

let f v (*@ req v>9; ens res>=100/\res<=110 @*) = 100

let f_fail () (* FIXME *) = apply f 10 (* Should give a specification of `req false` *)
