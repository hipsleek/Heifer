let hello5 ()
(*@ ens res=5 @*)
= (reset (shift k (fun x -> k x) + 2)) 3
