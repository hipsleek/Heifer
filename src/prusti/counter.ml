
(* https://github.com/FabianWolff/closure-examples/blob/master/counter.rs *)

let foo f
(*@ req f <: (fun v r (*@ ens r>=2 @*)) @*)
= ()

let counter_ok ()
(* Here, we cannot prove that the obligation (foo inc) will pass *)
= let x = ref 0 in
  let inc ()
  (*@ ex v; req x->v/\v>=0; ens x->v+1/\res=v @*)
  = let r = !x in x := !x + 1; r in
  inc ();
  inc ();
  (* assert (!x=2) *)
  foo inc

let counter_false () (* Entailment check is expected to fail **)
(*@ ens T @*)
= let x = ref 0 in
  let inc ()
  = let r = !x in x := !x + 1; r in
  inc ();
  (* assert (!x=1) *)
  foo inc
