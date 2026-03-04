let inc3 x
(*@ forall v. req x -> v; ens x -> v + 3; ens res = () @*)
= reset (
  let c = shift0 (fun k -> (k (fun () -> x := !x + 1; shift0 (fun _k0 -> (k (fun () -> ())))))) in
  x := !x + 1; c ())
