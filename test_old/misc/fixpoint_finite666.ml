

effect Foo : (unit -> unit)
effect Goo : (unit -> unit)
effect BefF : (unit -> unit)
effect AftF : (unit -> unit)
effect AftG : (unit -> unit)
effect Done : (unit -> unit)



let res12 ()
  (*@ requires (_^* ), eff(f)= (_^* ) -> Foo.Q(Foo()).Goo.Q(Goo()) @*)
  (*@ ensures Foo.BefF.Goo.Goo.Done.AftG.AftF @*)
  = match f () with
  | _ -> perform Done
  | effect Foo k ->  perform BefF; continue k 
    (fun () -> perform Goo ()); perform AftF
  | effect Goo k -> continue k (fun ()->()); perform AftG
