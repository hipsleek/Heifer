let hello4 ()
(*@ ens res=4 @*)
= (reset (shift k (fun x -> k x))) 4