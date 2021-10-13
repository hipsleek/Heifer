effect Foo0 : (unit -> unit)
effect Foo1 : (unit -> unit)
effect Foo2 : (unit -> unit)
effect Foo3 : (unit -> unit)

let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)
(*@ ensures  Foo0.(Foo1.Foo2.Foo3.Foo0)^w @*)
  = match f () with
 | _ -> ()
 | effect Foo0 k ->  continue k (fun () -> perform Foo1 ())
 | effect Foo1 k ->  continue k (fun () -> perform Foo2 ())
 | effect Foo2 k ->  continue k (fun () -> perform Foo3 ())
 | effect Foo3 k ->  continue k (fun () -> perform Foo0 ())