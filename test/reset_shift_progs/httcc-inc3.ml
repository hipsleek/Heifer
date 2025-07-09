let inc3 x
(*@ forall v. req x -> v; ens x -> v + 3; ens res = () @*)
= reset (
  let c = shift0 k (k (fun () -> x := !x + 1; shift0 _k (k (fun () -> ())))) in
  x := !x + 1; c ())
