
(* https://github.com/FabianWolff/closure-examples/blob/master/counter.rs *)

let foo f
(*@ ex v1 v2; f((), v1); f((), v2);
  req v1>=2/\v2>=2; ens res=v1+v2 @*)
= let v1 = f () in
  let v2 = f () in
  assert (v1 >= 2);
  assert (v2 >= 2);
  v1 + v2

let counter_ok ()
(*@ ens res=5 @*)
= let x = ref 0 in
  let inc ()
  (*@ ex v; req x->v; ens x->v+1/\res=v @*)
  = let r = !x in x := !x + 1; r in
  assert (!x = 0);
  inc ();
  assert (!x = 1);
  inc ();
  assert (!x = 2);
  (* Explicitly provide an instantiation of f as inc *)
  foo inc
