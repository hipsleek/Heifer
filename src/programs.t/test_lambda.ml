

let f ()
(*@ ens res=(fun x r -> ens r=1) @*)
= let _ = () in
  fun x (*@ ens res=x @*) -> x
