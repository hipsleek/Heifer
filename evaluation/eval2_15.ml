effect Foo0 : (unit -> unit)
effect Foo1 : (unit -> unit)
effect Foo2 : (unit -> unit)
effect Foo3 : (unit -> unit)
effect Foo4 : (unit -> unit)
effect Foo5 : (unit -> unit)
effect Foo6 : (unit -> unit)
effect Foo7 : (unit -> unit)
effect Foo8 : (unit -> unit)
effect Foo9 : (unit -> unit)
effect Foo10 : (unit -> unit)
effect Foo11 : (unit -> unit)
effect Foo12 : (unit -> unit)
effect Foo13 : (unit -> unit)
effect Foo14 : (unit -> unit)

let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)
(*@ ensures  ((((Foo0.Foo1.Foo3.Foo7) \/ (Foo0.Foo1.Foo3.Foo8)) \/ ((Foo0.Foo1.Foo4.Foo9) \/ (Foo0.Foo1.Foo4.Foo10))) \/ (((Foo0.Foo2.Foo5.Foo11) \/ (Foo0.Foo2.Foo5.Foo12)) \/ ((Foo0.Foo2.Foo6.Foo13) \/ (Foo0.Foo2.Foo6.Foo14)))) @*)
  = match f () with
 | _ -> ()
 | effect Foo0 k -> 
 continue k (fun () -> if true then perform Foo1() else perform Foo2 ())
 | effect Foo1 k -> 
 continue k (fun () -> if true then perform Foo3() else perform Foo4 ())
 | effect Foo2 k -> 
 continue k (fun () -> if true then perform Foo5() else perform Foo6 ())
 | effect Foo3 k -> 
 continue k (fun () -> if true then perform Foo7() else perform Foo8 ())
 | effect Foo4 k -> 
 continue k (fun () -> if true then perform Foo9() else perform Foo10 ())
 | effect Foo5 k -> 
 continue k (fun () -> if true then perform Foo11() else perform Foo12 ())
 | effect Foo6 k -> 
 continue k (fun () -> if true then perform Foo13() else perform Foo14 ())
 | effect Foo7 k ->  continue k (fun () -> ())
 | effect Foo8 k ->  continue k (fun () -> ())
 | effect Foo9 k ->  continue k (fun () -> ())
 | effect Foo10 k ->  continue k (fun () -> ())
 | effect Foo11 k ->  continue k (fun () -> ())
 | effect Foo12 k ->  continue k (fun () -> ())
 | effect Foo13 k ->  continue k (fun () -> ())
 | effect Foo14 k ->  continue k (fun () -> ())