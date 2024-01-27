
let closure_with_effects ()
(*@ ex i j; ens i->2*j->3/\res=5 @*)
= let i = ref 1 in
  let j = ref 2 in
  let cl x
  (*@
    ex a b; req x->a*j->b; ens j->b+a * x->a+1 /\ res=b+a+a+1
    \/ ex a; req x->a /\ x=j; ens j->a+a+1 /\ res=a+a+1+a+1
  @*)
  = j := !j + !x;
    x := !x + 1;
    !j + !x
  in
  cl i

let closures_with_local_state ()
(*@ ex i j; ens i->1 * j->2/\res=3 @*)
= let f =
    let x = ref 0 in
    fun () -> x := !x + 1; !x
  in
  let g =
    let x = ref 0 in
    fun () -> x := !x + 2; !x
  in
  f () + g ()

let private_aliased ()
(*@ ens res=4 @*)
= let counter =
    let x = ref 0 in
    fun () -> let r = !x in x := !x + 1; r
  in
  let x = ref 3 in
  counter ();
  counter () + !x