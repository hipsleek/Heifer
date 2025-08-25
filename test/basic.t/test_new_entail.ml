
(* basic *)

let test10 ()
  (*@ ens res=0 @*) =
  0
(* implicit normal stage *)

let test10_s ()
  (*@ ens emp/\res=0 @*) =
  0
(* res can also be used *)

let test6 ()
  (*@ ens res=0 @*) =
  let j = 0 in
  j
(* intermediate bindings don't matter *)

let test7_false ()
  (*@ ens res=j @*) =
  let j = 0 in
  j
(* j is not a param *)

let test8_false ()
  (*@ ens res=k @*) =
  let j = 0 in
  j
(* k is not a param *)

let test9 ()
  (*@ ex r. ens res=r @*) =
  let j = 0 in
  j
(* existential return value *)

let test4 ()
  (*@ ex i. ens i->0/\res=i @*) =
  let i = ref 0 in
  i
(* new heap location, hence existential *)

let test5 ()  (*@ ex i. ens i->0/\res=1 @*) =
  let i = ref 0 in
  !i + 1
(* heap read *)

let test61 ()  (*@ ex i. ens i->1/\res=1 @*) =
  let i = ref 0 in
  i := !i + 1;
  !i
(* heap update *)

let test23_false ()  (*@ ex i. ens i->1/\res=1 @*) =
  let i = ref 0 in
  i := !i + 2;
  !i
(* wrong value *)

let test13 ()
(*@ ex a b.
   ens a->0 * b->1/\res=1
@*)
=
  let i = ref 0 in
  let j = ref 1 in
  1

let test18 ()
(*@ ex a b.
   ens a->1+1 * b->0/\res=1
@*)
=
  let i = ref 0 in
  let j = ref 2 in
  1

let test20 ()
(*@ ex b.
   req i->1;
   ens i->1 * b->2/\res=1
@*)
=
  assertf "i -> 1";
  let j = ref 2 in
  1

let test21 ()
(*@ ex b.
   req i->1;
   ens i->1 * b->2/\res=1
@*)
=
  assertf "i -> 1";
  let j = ref 2 in
  assert (!j = 2);
  1

let test22 ()
(*@ ex i a.
   ens i->a/\res=()
@*)
=
  let j = ref 2 in
  let z = !j in
  assert (!j = z)

let test14_false ()
(*@ ex a b.
   ens a->1 * b->1/\res=1
@*)
=
  let i = ref 0 in
  let j = ref 1 in
  1

let test15 ()
(*@
   req a->1;
   ens a->1/\res=1
@*)
=
  assertf "a -> 1";
  1

(* this is unintuitive, but true as a consequence of the frame rule *)
let test16 ()
(*@ ex a.
   req a->1;
   ens a->1/\res=1
@*)
=
  let i = ref 0 in
  1

let test17 ()
(*@ ex b.
   req a->1;
   ens a->1 * b->0/\res=1
@*)
=
  assertf "a -> 1";
  let i = ref 0 in
  1

let f1 () (*@ ens emp/\res=1 @*) = 1

let test24 ()  (*@ ens emp/\res=1 @*) =
  let ret = f1 () in
  ret

let fa a (*@ req a=1/\emp; ens emp/\res=2 @*) = a + 1

let test26 ()  (*@ ens emp/\res=2 @*) =
  let ret = fa 1 in
  ret

let if_disj b
(*@ ens emp/\res=1 \/ ens emp/\res=2
@*)
= if b then 1 else 2

let if_let x
(*@ ens emp/\res=1 \/ ens emp/\res=2 @*)
= let y = not x in
  if y then 1 else 2

let foo1 xs = 1
let foo2 xs (*@ ens res=1 @*) = 1

let goo1 xs
(*@ let t = foo1(xs) in ens res=t @*)
= foo1 xs

let goo2 xs
(*@ let t = foo2(xs) in ens res=t @*)
= foo2 xs

let call_f_in_g ()
(*@ ens res=5 @*)
= let x = 3 in
  let f x = x in
  f 5

let call_ret f (*@ let v = f(100) in ens res=v @*) =
  f 100

let test_non_rec_pred ()
(*@ ens res=100 @*)
= let id i = i in
  id 2;

  call_ret id

let test_read x
  (*@ forall a. req x->a; ens x->a/\res=a @*) =
  let j = !x in
  j
