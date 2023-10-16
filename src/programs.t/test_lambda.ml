

let f1 ()
(*@ ens res=(fun x r -> ens r=x) @*)
= let _ = () in
  fun x (*@ ens res=x @*) -> x

let f2 ()
(*@ ens res=2 @*)
=
  let f3 = f1 () in
  f3 2
