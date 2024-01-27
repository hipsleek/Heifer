
let closure_list ()
(*@ ex i; ens i->[8;7;42]/\res=[8;7;42] @*)
= let l = ref [] in
  l := 42 :: !l;
  let f i = l := i :: !l in
  let g h x = h x; l := (x+1) :: !l in
  g f 7;
  !l
