effect Foo0 : (unit -> unit)
effect Foo1 : (unit -> unit)
effect Foo2 : (unit -> unit)
effect Foo3 : (unit -> unit)
effect Foo4 : (unit -> unit)
effect Foo5 : (unit -> unit)
effect Foo6 : (unit -> unit)

let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)
(*@ ensures  (((Foo0.Foo1.Foo3) \/ (Foo0.Foo1.Foo4)) \/ ((Foo0.Foo2.Foo5) \/ (Foo0.Foo2.Foo6))) @*)
  = match f () with
 | _ -> ()
 | effect Foo0 k -> 
 continue k (fun () -> if true then perform Foo1() else perform Foo2 ())
 | effect Foo1 k -> 
 continue k (fun () -> if true then perform Foo3() else perform Foo4 ())
 | effect Foo2 k -> 
 continue k (fun () -> if true then perform Foo5() else perform Foo6 ())
 | effect Foo3 k ->  continue k (fun () -> ())
 | effect Foo4 k ->  continue k (fun () -> ())
 | effect Foo5 k ->  continue k (fun () -> ())
 | effect Foo6 k ->  continue k (fun () -> ())