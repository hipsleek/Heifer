effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let res f
(*@ requires emp, eff(f)= _^* -> Foo.Q(Foo ())  @*)
(*@ ensures  (Foo.Goo)^w @*)
= match f () with
| _ -> ()
| effect Foo k -> continue k 
      (fun () -> perform Goo ())
| effect Goo k -> continue k 
      (fun () -> perform Foo ())

