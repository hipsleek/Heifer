

let f1 ()
(*@ ex i. ens i->[]/\res=[] @*)
= let l = ref [] in
  !l

let f2 ()
(*@ ex i. ens i->[42]/\res=[42] @*)
= let l = ref [] in
  l := 42 :: !l;
  !l

let f3 ()
(*@ ex i. ens i->[42]/\res=[42] @*)
= let l = ref [] in
  let f () = l := 42 :: !l in
  f ();
  !l

let f4 ()
(*@ ex i. ens i->[42]/\res=[42] @*)
= let l = ref [] in
  let f () = l := 42 :: !l in
  let g h = h () in
  g f;
  !l

let f5_false ()
(*@ ex i. ens i->[41]/\res=[42] @*)
= let l = ref [] in
  let f () = l := 42 :: !l in
  let g h = h () in
  g f;
  !l

let f6 ()
(*@ ex i. ens i->[1;42;0]/\res=[1;42;0] @*)
= let l = ref [0] in
  let f () = l := 42 :: !l in
  let g h = h (); l := 1 :: !l in
  g f;
  !l

let f7 ()
(*@ ex i. ens i->[8;7;42]/\res=[8;7;42] @*)
= let l = ref [] in
  l := 42 :: !l;
  let f i = l := i :: !l in
  let g h x = h x; l := (x+1) :: !l in
  g f 7;
  !l

let apply f x = f x

let f8 ()
(*@ ex l. ens l->1/\res=1 @*)
= let l = ref 0 in
  (* let apply f x = f x in *)
  let cl x = l := !l + x; !l in
  apply cl 1
