

let f ()
(*@ ens res=(fun x -> ens res=x) @*)
= let _ = () in
  fun x (*@ ens res=x @*) -> x
