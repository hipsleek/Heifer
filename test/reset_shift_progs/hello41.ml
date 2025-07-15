let hello41 ()
(*@ ens res=4 @*)
= let f x = x + x in
  (reset (shift (fun k -> (fun x -> k (f x))))) 2
