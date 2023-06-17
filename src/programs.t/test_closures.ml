
(* let f1 ()
(*@ ex i; Norm(i->[], []) @*)
= let l = ref [] in
  !l

let f2 ()
(*@ ex i; Norm(i->[42], [42]) @*)
= let l = ref [] in
  l := 42 :: !l;
  !l

let f3 ()
(*@ ex i; Norm(i->[42], [42]) @*)
= let l = ref [] in
  let f () = l := 42 :: !l in
  f ();
  !l

let f4 ()
(*@ ex i; Norm(i->[42], [42]) @*)
= let l = ref [] in
  let f () = l := 42 :: !l in
  let g h = h () in
  g f;
  !l

let f5_false ()
(*@ ex i; Norm(i->[41], [42]) @*)
= let l = ref [] in
  let f () = l := 42 :: !l in
  let g h = h () in
  g f;
  !l

let f6 ()
(*@ ex i; Norm(i->[1;42;0], [1;42;0]) @*)
= let l = ref [0] in
  let f () = l := 42 :: !l in
  let g h = h (); l := 1 :: !l in
  g f;
  !l

let f7 ()
(*@ ex i; Norm(i->[8;7;42], [8;7;42]) @*)
= let l = ref [] in
  l := 42 :: !l;
  let f i = l := i :: !l in
  let g h x = h x; l := (x+1) :: !l in
  g f 7;
  !l *)

let apply f x = f x

let f8 ()
(*@ ex l; Norm(l->1, 1) @*)
= let l = ref 0 in
  (* let apply f x = f x in *)
  let cl x = l := !l + x; !l in
  apply cl 1

