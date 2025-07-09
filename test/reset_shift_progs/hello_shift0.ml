let hello_shift0 ()
(*@ ens res="A cat has Alice." @*)
= reset ("Alice" ^ reset ("has " ^ shift0 k1 (shift0 k2 ("A cat " ^ k1 (k2 ".")))))
