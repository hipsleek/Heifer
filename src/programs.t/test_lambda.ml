

let f ()
(*@ ens res=(fun x r -> ens r=x) @*)
= let _ = () in
  fun x (*@ ens res=x @*) -> x
