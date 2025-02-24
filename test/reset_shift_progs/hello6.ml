let hello6 ()
(*@ ens res=6 @*)
= ((reset (shift k (fun x -> k x) + shift k (fun x -> k x))) 2) 4
