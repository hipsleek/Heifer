
(* https://github.com/FabianWolff/closure-examples/blob/master/blameassgn.rs *)

(* let g_f_x? f x
(*@ req x->_ * f <: (fun v r -> req v>9; ens r>=0/\r<=99) @*)
= f 0 *)

(* let g_f_x? f x
(*@ req x->_ * f <: (fun v r -> x->v ... req v>9; ens r>=0/\r<=99) @*)
= f 0 *)

let g_false f
(*@ req f <: (fun v r (*@ req v>9; ens r>=0/\r<=99 @*) ) @*)
= f 0

let g f
(*@ req f <: (fun v r (*@ req v>9; ens r>=0/\r<=99 @*) ); ens res>=0/\res<=99 @*)
= f 10

let h v
(*@ req v>9; ens res>=50/\res<=99 @*)
= 66

let g_h_ok ()
(*@ ens res>=0/\res<=99 @*)
= g h

let f v
(*@ req v>9; ens res>=10-20/\res<=89 @*)
= 10-20

let g_f_false ()
(*@ ens res>=0/\res<=99 @*)
= g f