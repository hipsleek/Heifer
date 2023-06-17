
(* let main ()
(*@ Norm(emp, 0) @*)
=
let l = ref 0 in
(* l := !l + 1; *)
(* l := !l + 1; *)
let f i = !l in
!l *)

(* let main ()
(*@ Norm(emp, [1]) @*)
=
let l = ref [1] in
(* let f i = l := i :: !l; !l in *)
let f i = !l in
f 1 *)

let main ()
(*@ ex i; Norm(i->[8;7;42], [8;7;42]) @*)
= let l = ref [] in
  l := 42 :: !l;
  let f i = l := i :: !l in
  let g h x = h x; l := (x+1) :: !l in
  g f 7;
  (* assert (!l = [8;7;42]); *)
  !l
