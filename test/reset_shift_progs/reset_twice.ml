let reset_twice ()
(*@ ens res=5 @*)
= reset (1 + reset (2 + shift k (k 0 + k 0)))
