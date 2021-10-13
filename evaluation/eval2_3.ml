effect Foo0 : (unit -> unit)
effect Foo1 : (unit -> unit)
effect Foo2 : (unit -> unit)

let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)
(*@ ensures  ((Foo0.Foo1) \/ (Foo0.Foo2)) @*)
  = match f () with
 | _ -> ()
 | effect Foo0 k -> 
 continue k (fun () -> if true then perform Foo1() else perform Foo2 ())
 | effect Foo1 k ->  continue k (fun () -> ())
 | effect Foo2 k ->  continue k (fun () -> ())