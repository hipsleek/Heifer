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
effect Foo15 : (unit -> unit)
effect Foo16 : (unit -> unit)
effect Foo17 : (unit -> unit)
effect Foo18 : (unit -> unit)
effect Foo19 : (unit -> unit)
effect Foo20 : (unit -> unit)
effect Foo21 : (unit -> unit)
effect Foo22 : (unit -> unit)
effect Foo23 : (unit -> unit)
effect Foo24 : (unit -> unit)
effect Foo25 : (unit -> unit)
effect Foo26 : (unit -> unit)
effect Foo27 : (unit -> unit)
effect Foo28 : (unit -> unit)
effect Foo29 : (unit -> unit)
effect Foo30 : (unit -> unit)

let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)
(*@ ensures  (((((Foo0.Foo1.Foo3.Foo7.Foo15) \/ (Foo0.Foo1.Foo3.Foo7.Foo16)) \/ ((Foo0.Foo1.Foo3.Foo8.Foo17) \/ (Foo0.Foo1.Foo3.Foo8.Foo18))) \/ (((Foo0.Foo1.Foo4.Foo9.Foo19) \/ (Foo0.Foo1.Foo4.Foo9.Foo20)) \/ ((Foo0.Foo1.Foo4.Foo10.Foo21) \/ (Foo0.Foo1.Foo4.Foo10.Foo22)))) \/ ((((Foo0.Foo2.Foo5.Foo11.Foo23) \/ (Foo0.Foo2.Foo5.Foo11.Foo24)) \/ ((Foo0.Foo2.Foo5.Foo12.Foo25) \/ (Foo0.Foo2.Foo5.Foo12.Foo26))) \/ (((Foo0.Foo2.Foo6.Foo13.Foo27) \/ (Foo0.Foo2.Foo6.Foo13.Foo28)) \/ ((Foo0.Foo2.Foo6.Foo14.Foo29) \/ (Foo0.Foo2.Foo6.Foo14.Foo30))))) @*)
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
 | effect Foo7 k -> 
 continue k (fun () -> if true then perform Foo15() else perform Foo16 ())
 | effect Foo8 k -> 
 continue k (fun () -> if true then perform Foo17() else perform Foo18 ())
 | effect Foo9 k -> 
 continue k (fun () -> if true then perform Foo19() else perform Foo20 ())
 | effect Foo10 k -> 
 continue k (fun () -> if true then perform Foo21() else perform Foo22 ())
 | effect Foo11 k -> 
 continue k (fun () -> if true then perform Foo23() else perform Foo24 ())
 | effect Foo12 k -> 
 continue k (fun () -> if true then perform Foo25() else perform Foo26 ())
 | effect Foo13 k -> 
 continue k (fun () -> if true then perform Foo27() else perform Foo28 ())
 | effect Foo14 k -> 
 continue k (fun () -> if true then perform Foo29() else perform Foo30 ())
 | effect Foo15 k ->  continue k (fun () -> ())
 | effect Foo16 k ->  continue k (fun () -> ())
 | effect Foo17 k ->  continue k (fun () -> ())
 | effect Foo18 k ->  continue k (fun () -> ())
 | effect Foo19 k ->  continue k (fun () -> ())
 | effect Foo20 k ->  continue k (fun () -> ())
 | effect Foo21 k ->  continue k (fun () -> ())
 | effect Foo22 k ->  continue k (fun () -> ())
 | effect Foo23 k ->  continue k (fun () -> ())
 | effect Foo24 k ->  continue k (fun () -> ())
 | effect Foo25 k ->  continue k (fun () -> ())
 | effect Foo26 k ->  continue k (fun () -> ())
 | effect Foo27 k ->  continue k (fun () -> ())
 | effect Foo28 k ->  continue k (fun () -> ())
 | effect Foo29 k ->  continue k (fun () -> ())
 | effect Foo30 k ->  continue k (fun () -> ())