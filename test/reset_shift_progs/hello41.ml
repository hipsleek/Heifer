let hello41 ()
(*@ ens res=4 @*)
= let f x = x + x in
  (reset (shift k (fun x -> k (f x)))) 2
