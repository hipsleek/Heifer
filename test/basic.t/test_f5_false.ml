let f5_false ()
(*@ ex i. ens i->[41]/\res=[42] @*)
= let l = ref [] in
  let f () = l := 42 :: !l in
  let g h = h () in
  g f;
  !l
