
let closures ()
(*@ ex i; Norm(i->[8;7;42], [8;7;42]) @*)
= let l = ref [] in
  l := 42 :: !l;
  let f i = l := i :: !l in
  let g h x = h x; l := (x+1) :: !l in
  g f 7;
  (* assert (!l = [8;7;42]); *)
  !l

let closures_with_local_state ()
(*@ ex i j; Norm(i->1 * j->2, 3) @*)
= let f =
    let x = ref 0 in
    fun () -> x := !x + 1; !x
  in
  let g =
    let x = ref 0 in
    fun () -> x := !x + 2; !x
  in
  f () + g ()

let simple_closures ()
(*@ Norm(emp, 4) @*)
= let counter =
    let x = ref 0 in
    fun () -> let r = !x in x := !x + 1; r
  in
  let x = ref 3 in
  counter ();
  counter () + !x

(* Section 2.2.1 in Modular Specification and Verification of Closures in Rust *)
let closure_with_effects () (* FIXME *)
(*@ req i->1*j->2; ens i->2*j->3/\res=5 @*)
= let i = ref 1 in
  let j = ref 2 in
  let cl x =
    j := !j + !x;
    x := !x + 1;
    !j + !x in
  cl i

(* https://ilyasergey.net/CS6217/_static/slides/04-FunLog.pdf *)
let min_max_plus x y min max
(*@ ex a b; req min->a*max->b; ex i j; ens min->i*max->j/\i<=j/\res=x+y @*)
= let min' = if x < y then x else y in
  let max' = if x < y then y else x in
  min := min';
  max := max';
  x + y
