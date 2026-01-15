let f3 ()
(*@ ex i. ens i->[42]/\res=[42] @*)
= let l = ref [] in
  let f () = l := 42 :: !l in
  f ();
  !l
