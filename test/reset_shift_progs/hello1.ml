let hello1 ()
(*@ ens res=2 @*)
= reset (1 + shift (fun k -> k 1))
