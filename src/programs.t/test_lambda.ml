

let f ()
(*@ ens res=(fun x r -> ens r=x) @*)
= let _ = () in
  fun x (*@ ens res=x @*) -> x

let g ()
(*@ ens res=2 @*)
=
  let h = f () in
  h 2