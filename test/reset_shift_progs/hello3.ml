let hello3 ()
(*@ ens res=3 @*)
= let f x = x + x in
  reset (1 + shift k (k (f 1)))
