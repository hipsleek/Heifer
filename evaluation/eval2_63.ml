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
effect Foo31 : (unit -> unit)
effect Foo32 : (unit -> unit)
effect Foo33 : (unit -> unit)
effect Foo34 : (unit -> unit)
effect Foo35 : (unit -> unit)
effect Foo36 : (unit -> unit)
effect Foo37 : (unit -> unit)
effect Foo38 : (unit -> unit)
effect Foo39 : (unit -> unit)
effect Foo40 : (unit -> unit)
effect Foo41 : (unit -> unit)
effect Foo42 : (unit -> unit)
effect Foo43 : (unit -> unit)
effect Foo44 : (unit -> unit)
effect Foo45 : (unit -> unit)
effect Foo46 : (unit -> unit)
effect Foo47 : (unit -> unit)
effect Foo48 : (unit -> unit)
effect Foo49 : (unit -> unit)
effect Foo50 : (unit -> unit)
effect Foo51 : (unit -> unit)
effect Foo52 : (unit -> unit)
effect Foo53 : (unit -> unit)
effect Foo54 : (unit -> unit)
effect Foo55 : (unit -> unit)
effect Foo56 : (unit -> unit)
effect Foo57 : (unit -> unit)
effect Foo58 : (unit -> unit)
effect Foo59 : (unit -> unit)
effect Foo60 : (unit -> unit)
effect Foo61 : (unit -> unit)
effect Foo62 : (unit -> unit)

let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)
(*@ ensures  ((((((Foo0.Foo1.Foo3.Foo7.Foo15.Foo31) \/ (Foo0.Foo1.Foo3.Foo7.Foo15.Foo32)) \/ ((Foo0.Foo1.Foo3.Foo7.Foo16.Foo33) \/ (Foo0.Foo1.Foo3.Foo7.Foo16.Foo34))) \/ (((Foo0.Foo1.Foo3.Foo8.Foo17.Foo35) \/ (Foo0.Foo1.Foo3.Foo8.Foo17.Foo36)) \/ ((Foo0.Foo1.Foo3.Foo8.Foo18.Foo37) \/ (Foo0.Foo1.Foo3.Foo8.Foo18.Foo38)))) \/ ((((Foo0.Foo1.Foo4.Foo9.Foo19.Foo39) \/ (Foo0.Foo1.Foo4.Foo9.Foo19.Foo40)) \/ ((Foo0.Foo1.Foo4.Foo9.Foo20.Foo41) \/ (Foo0.Foo1.Foo4.Foo9.Foo20.Foo42))) \/ (((Foo0.Foo1.Foo4.Foo10.Foo21.Foo43) \/ (Foo0.Foo1.Foo4.Foo10.Foo21.Foo44)) \/ ((Foo0.Foo1.Foo4.Foo10.Foo22.Foo45) \/ (Foo0.Foo1.Foo4.Foo10.Foo22.Foo46))))) \/ (((((Foo0.Foo2.Foo5.Foo11.Foo23.Foo47) \/ (Foo0.Foo2.Foo5.Foo11.Foo23.Foo48)) \/ ((Foo0.Foo2.Foo5.Foo11.Foo24.Foo49) \/ (Foo0.Foo2.Foo5.Foo11.Foo24.Foo50))) \/ (((Foo0.Foo2.Foo5.Foo12.Foo25.Foo51) \/ (Foo0.Foo2.Foo5.Foo12.Foo25.Foo52)) \/ ((Foo0.Foo2.Foo5.Foo12.Foo26.Foo53) \/ (Foo0.Foo2.Foo5.Foo12.Foo26.Foo54)))) \/ ((((Foo0.Foo2.Foo6.Foo13.Foo27.Foo55) \/ (Foo0.Foo2.Foo6.Foo13.Foo27.Foo56)) \/ ((Foo0.Foo2.Foo6.Foo13.Foo28.Foo57) \/ (Foo0.Foo2.Foo6.Foo13.Foo28.Foo58))) \/ (((Foo0.Foo2.Foo6.Foo14.Foo29.Foo59) \/ (Foo0.Foo2.Foo6.Foo14.Foo29.Foo60)) \/ ((Foo0.Foo2.Foo6.Foo14.Foo30.Foo61) \/ (Foo0.Foo2.Foo6.Foo14.Foo30.Foo62)))))) @*)
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
 | effect Foo15 k -> 
 continue k (fun () -> if true then perform Foo31() else perform Foo32 ())
 | effect Foo16 k -> 
 continue k (fun () -> if true then perform Foo33() else perform Foo34 ())
 | effect Foo17 k -> 
 continue k (fun () -> if true then perform Foo35() else perform Foo36 ())
 | effect Foo18 k -> 
 continue k (fun () -> if true then perform Foo37() else perform Foo38 ())
 | effect Foo19 k -> 
 continue k (fun () -> if true then perform Foo39() else perform Foo40 ())
 | effect Foo20 k -> 
 continue k (fun () -> if true then perform Foo41() else perform Foo42 ())
 | effect Foo21 k -> 
 continue k (fun () -> if true then perform Foo43() else perform Foo44 ())
 | effect Foo22 k -> 
 continue k (fun () -> if true then perform Foo45() else perform Foo46 ())
 | effect Foo23 k -> 
 continue k (fun () -> if true then perform Foo47() else perform Foo48 ())
 | effect Foo24 k -> 
 continue k (fun () -> if true then perform Foo49() else perform Foo50 ())
 | effect Foo25 k -> 
 continue k (fun () -> if true then perform Foo51() else perform Foo52 ())
 | effect Foo26 k -> 
 continue k (fun () -> if true then perform Foo53() else perform Foo54 ())
 | effect Foo27 k -> 
 continue k (fun () -> if true then perform Foo55() else perform Foo56 ())
 | effect Foo28 k -> 
 continue k (fun () -> if true then perform Foo57() else perform Foo58 ())
 | effect Foo29 k -> 
 continue k (fun () -> if true then perform Foo59() else perform Foo60 ())
 | effect Foo30 k -> 
 continue k (fun () -> if true then perform Foo61() else perform Foo62 ())
 | effect Foo31 k ->  continue k (fun () -> ())
 | effect Foo32 k ->  continue k (fun () -> ())
 | effect Foo33 k ->  continue k (fun () -> ())
 | effect Foo34 k ->  continue k (fun () -> ())
 | effect Foo35 k ->  continue k (fun () -> ())
 | effect Foo36 k ->  continue k (fun () -> ())
 | effect Foo37 k ->  continue k (fun () -> ())
 | effect Foo38 k ->  continue k (fun () -> ())
 | effect Foo39 k ->  continue k (fun () -> ())
 | effect Foo40 k ->  continue k (fun () -> ())
 | effect Foo41 k ->  continue k (fun () -> ())
 | effect Foo42 k ->  continue k (fun () -> ())
 | effect Foo43 k ->  continue k (fun () -> ())
 | effect Foo44 k ->  continue k (fun () -> ())
 | effect Foo45 k ->  continue k (fun () -> ())
 | effect Foo46 k ->  continue k (fun () -> ())
 | effect Foo47 k ->  continue k (fun () -> ())
 | effect Foo48 k ->  continue k (fun () -> ())
 | effect Foo49 k ->  continue k (fun () -> ())
 | effect Foo50 k ->  continue k (fun () -> ())
 | effect Foo51 k ->  continue k (fun () -> ())
 | effect Foo52 k ->  continue k (fun () -> ())
 | effect Foo53 k ->  continue k (fun () -> ())
 | effect Foo54 k ->  continue k (fun () -> ())
 | effect Foo55 k ->  continue k (fun () -> ())
 | effect Foo56 k ->  continue k (fun () -> ())
 | effect Foo57 k ->  continue k (fun () -> ())
 | effect Foo58 k ->  continue k (fun () -> ())
 | effect Foo59 k ->  continue k (fun () -> ())
 | effect Foo60 k ->  continue k (fun () -> ())
 | effect Foo61 k ->  continue k (fun () -> ())
 | effect Foo62 k ->  continue k (fun () -> ())