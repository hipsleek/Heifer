
(* https://github.com/FabianWolff/closure-examples/blob/master/counter.rs *)

let foo f
= let inner v (*@ req v>=2; ens res>=2 @*)  = v in
  inner (f ())

let counter_ok ()
= let x = ref 0 in
  let inc ()
  (*@ ex v; req x->v; ens x->v+1/\res=v @*)
  = let r = !x in x := !x + 1; r in
  inc ();
  inc ();
  foo inc

let counter_fail () (* FIXME *)
= let x = ref 0 in
  let inc ()
  (*@ ex v; req x->v; ens x->v+1/\res=v @*)
  = let r = !x in x := !x + 1; r in
  inc ();
  foo inc
