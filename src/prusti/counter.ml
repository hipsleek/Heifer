
(* https://github.com/FabianWolff/closure-examples/blob/master/counter.rs *)

let foo f
(*@ req f <: (fun v r (*@ ens r>=2 @*)) @*)
= ()

let counter_ok () (* FIXME *)
(*@ ens T @*)
= let x = ref 0 in
  let inc ()
  (*@ ex v; req x->v/\v>=0; ens x->v+1/\res=v @*)
  = let r = !x in x := !x + 1; r in
  inc ();
  inc ();
  foo inc (* Succeeds because the result of the closure is 2 *)

let counter_false ()
(*@ ens T @*)
= let x = ref 0 in
  let inc ()
  (*@ ex v; req x->v/\v>=0; ens x->v+1/\res=v @*)
  = let r = !x in x := !x + 1; r in
  inc ();
  foo inc (* Fails because the result of the closure is 1 *)
