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
effect Foo63 : (unit -> unit)
effect Foo64 : (unit -> unit)
effect Foo65 : (unit -> unit)
effect Foo66 : (unit -> unit)
effect Foo67 : (unit -> unit)
effect Foo68 : (unit -> unit)
effect Foo69 : (unit -> unit)
effect Foo70 : (unit -> unit)
effect Foo71 : (unit -> unit)
effect Foo72 : (unit -> unit)
effect Foo73 : (unit -> unit)
effect Foo74 : (unit -> unit)
effect Foo75 : (unit -> unit)
effect Foo76 : (unit -> unit)
effect Foo77 : (unit -> unit)
effect Foo78 : (unit -> unit)
effect Foo79 : (unit -> unit)
effect Foo80 : (unit -> unit)
effect Foo81 : (unit -> unit)
effect Foo82 : (unit -> unit)
effect Foo83 : (unit -> unit)
effect Foo84 : (unit -> unit)
effect Foo85 : (unit -> unit)
effect Foo86 : (unit -> unit)
effect Foo87 : (unit -> unit)
effect Foo88 : (unit -> unit)
effect Foo89 : (unit -> unit)
effect Foo90 : (unit -> unit)
effect Foo91 : (unit -> unit)
effect Foo92 : (unit -> unit)
effect Foo93 : (unit -> unit)
effect Foo94 : (unit -> unit)
effect Foo95 : (unit -> unit)
effect Foo96 : (unit -> unit)
effect Foo97 : (unit -> unit)
effect Foo98 : (unit -> unit)
effect Foo99 : (unit -> unit)
effect Foo100 : (unit -> unit)
effect Foo101 : (unit -> unit)
effect Foo102 : (unit -> unit)
effect Foo103 : (unit -> unit)
effect Foo104 : (unit -> unit)
effect Foo105 : (unit -> unit)
effect Foo106 : (unit -> unit)
effect Foo107 : (unit -> unit)
effect Foo108 : (unit -> unit)
effect Foo109 : (unit -> unit)
effect Foo110 : (unit -> unit)
effect Foo111 : (unit -> unit)
effect Foo112 : (unit -> unit)
effect Foo113 : (unit -> unit)
effect Foo114 : (unit -> unit)
effect Foo115 : (unit -> unit)
effect Foo116 : (unit -> unit)
effect Foo117 : (unit -> unit)
effect Foo118 : (unit -> unit)
effect Foo119 : (unit -> unit)
effect Foo120 : (unit -> unit)
effect Foo121 : (unit -> unit)
effect Foo122 : (unit -> unit)
effect Foo123 : (unit -> unit)
effect Foo124 : (unit -> unit)
effect Foo125 : (unit -> unit)
effect Foo126 : (unit -> unit)

let stress f
(*@ requires _^*, eff(f)= (_^* ) -> Foo0.Q(Foo0()) @*)
(*@ ensures  (((((((Foo0.Foo1.Foo3.Foo7.Foo15.Foo31.Foo63) \/ (Foo0.Foo1.Foo3.Foo7.Foo15.Foo31.Foo64)) \/ ((Foo0.Foo1.Foo3.Foo7.Foo15.Foo32.Foo65) \/ (Foo0.Foo1.Foo3.Foo7.Foo15.Foo32.Foo66))) \/ (((Foo0.Foo1.Foo3.Foo7.Foo16.Foo33.Foo67) \/ (Foo0.Foo1.Foo3.Foo7.Foo16.Foo33.Foo68)) \/ ((Foo0.Foo1.Foo3.Foo7.Foo16.Foo34.Foo69) \/ (Foo0.Foo1.Foo3.Foo7.Foo16.Foo34.Foo70)))) \/ ((((Foo0.Foo1.Foo3.Foo8.Foo17.Foo35.Foo71) \/ (Foo0.Foo1.Foo3.Foo8.Foo17.Foo35.Foo72)) \/ ((Foo0.Foo1.Foo3.Foo8.Foo17.Foo36.Foo73) \/ (Foo0.Foo1.Foo3.Foo8.Foo17.Foo36.Foo74))) \/ (((Foo0.Foo1.Foo3.Foo8.Foo18.Foo37.Foo75) \/ (Foo0.Foo1.Foo3.Foo8.Foo18.Foo37.Foo76)) \/ ((Foo0.Foo1.Foo3.Foo8.Foo18.Foo38.Foo77) \/ (Foo0.Foo1.Foo3.Foo8.Foo18.Foo38.Foo78))))) \/ (((((Foo0.Foo1.Foo4.Foo9.Foo19.Foo39.Foo79) \/ (Foo0.Foo1.Foo4.Foo9.Foo19.Foo39.Foo80)) \/ ((Foo0.Foo1.Foo4.Foo9.Foo19.Foo40.Foo81) \/ (Foo0.Foo1.Foo4.Foo9.Foo19.Foo40.Foo82))) \/ (((Foo0.Foo1.Foo4.Foo9.Foo20.Foo41.Foo83) \/ (Foo0.Foo1.Foo4.Foo9.Foo20.Foo41.Foo84)) \/ ((Foo0.Foo1.Foo4.Foo9.Foo20.Foo42.Foo85) \/ (Foo0.Foo1.Foo4.Foo9.Foo20.Foo42.Foo86)))) \/ ((((Foo0.Foo1.Foo4.Foo10.Foo21.Foo43.Foo87) \/ (Foo0.Foo1.Foo4.Foo10.Foo21.Foo43.Foo88)) \/ ((Foo0.Foo1.Foo4.Foo10.Foo21.Foo44.Foo89) \/ (Foo0.Foo1.Foo4.Foo10.Foo21.Foo44.Foo90))) \/ (((Foo0.Foo1.Foo4.Foo10.Foo22.Foo45.Foo91) \/ (Foo0.Foo1.Foo4.Foo10.Foo22.Foo45.Foo92)) \/ ((Foo0.Foo1.Foo4.Foo10.Foo22.Foo46.Foo93) \/ (Foo0.Foo1.Foo4.Foo10.Foo22.Foo46.Foo94)))))) \/ ((((((Foo0.Foo2.Foo5.Foo11.Foo23.Foo47.Foo95) \/ (Foo0.Foo2.Foo5.Foo11.Foo23.Foo47.Foo96)) \/ ((Foo0.Foo2.Foo5.Foo11.Foo23.Foo48.Foo97) \/ (Foo0.Foo2.Foo5.Foo11.Foo23.Foo48.Foo98))) \/ (((Foo0.Foo2.Foo5.Foo11.Foo24.Foo49.Foo99) \/ (Foo0.Foo2.Foo5.Foo11.Foo24.Foo49.Foo100)) \/ ((Foo0.Foo2.Foo5.Foo11.Foo24.Foo50.Foo101) \/ (Foo0.Foo2.Foo5.Foo11.Foo24.Foo50.Foo102)))) \/ ((((Foo0.Foo2.Foo5.Foo12.Foo25.Foo51.Foo103) \/ (Foo0.Foo2.Foo5.Foo12.Foo25.Foo51.Foo104)) \/ ((Foo0.Foo2.Foo5.Foo12.Foo25.Foo52.Foo105) \/ (Foo0.Foo2.Foo5.Foo12.Foo25.Foo52.Foo106))) \/ (((Foo0.Foo2.Foo5.Foo12.Foo26.Foo53.Foo107) \/ (Foo0.Foo2.Foo5.Foo12.Foo26.Foo53.Foo108)) \/ ((Foo0.Foo2.Foo5.Foo12.Foo26.Foo54.Foo109) \/ (Foo0.Foo2.Foo5.Foo12.Foo26.Foo54.Foo110))))) \/ (((((Foo0.Foo2.Foo6.Foo13.Foo27.Foo55.Foo111) \/ (Foo0.Foo2.Foo6.Foo13.Foo27.Foo55.Foo112)) \/ ((Foo0.Foo2.Foo6.Foo13.Foo27.Foo56.Foo113) \/ (Foo0.Foo2.Foo6.Foo13.Foo27.Foo56.Foo114))) \/ (((Foo0.Foo2.Foo6.Foo13.Foo28.Foo57.Foo115) \/ (Foo0.Foo2.Foo6.Foo13.Foo28.Foo57.Foo116)) \/ ((Foo0.Foo2.Foo6.Foo13.Foo28.Foo58.Foo117) \/ (Foo0.Foo2.Foo6.Foo13.Foo28.Foo58.Foo118)))) \/ ((((Foo0.Foo2.Foo6.Foo14.Foo29.Foo59.Foo119) \/ (Foo0.Foo2.Foo6.Foo14.Foo29.Foo59.Foo120)) \/ ((Foo0.Foo2.Foo6.Foo14.Foo29.Foo60.Foo121) \/ (Foo0.Foo2.Foo6.Foo14.Foo29.Foo60.Foo122))) \/ (((Foo0.Foo2.Foo6.Foo14.Foo30.Foo61.Foo123) \/ (Foo0.Foo2.Foo6.Foo14.Foo30.Foo61.Foo124)) \/ ((Foo0.Foo2.Foo6.Foo14.Foo30.Foo62.Foo125) \/ (Foo0.Foo2.Foo6.Foo14.Foo30.Foo62.Foo126))))))) @*)
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
 | effect Foo31 k -> 
 continue k (fun () -> if true then perform Foo63() else perform Foo64 ())
 | effect Foo32 k -> 
 continue k (fun () -> if true then perform Foo65() else perform Foo66 ())
 | effect Foo33 k -> 
 continue k (fun () -> if true then perform Foo67() else perform Foo68 ())
 | effect Foo34 k -> 
 continue k (fun () -> if true then perform Foo69() else perform Foo70 ())
 | effect Foo35 k -> 
 continue k (fun () -> if true then perform Foo71() else perform Foo72 ())
 | effect Foo36 k -> 
 continue k (fun () -> if true then perform Foo73() else perform Foo74 ())
 | effect Foo37 k -> 
 continue k (fun () -> if true then perform Foo75() else perform Foo76 ())
 | effect Foo38 k -> 
 continue k (fun () -> if true then perform Foo77() else perform Foo78 ())
 | effect Foo39 k -> 
 continue k (fun () -> if true then perform Foo79() else perform Foo80 ())
 | effect Foo40 k -> 
 continue k (fun () -> if true then perform Foo81() else perform Foo82 ())
 | effect Foo41 k -> 
 continue k (fun () -> if true then perform Foo83() else perform Foo84 ())
 | effect Foo42 k -> 
 continue k (fun () -> if true then perform Foo85() else perform Foo86 ())
 | effect Foo43 k -> 
 continue k (fun () -> if true then perform Foo87() else perform Foo88 ())
 | effect Foo44 k -> 
 continue k (fun () -> if true then perform Foo89() else perform Foo90 ())
 | effect Foo45 k -> 
 continue k (fun () -> if true then perform Foo91() else perform Foo92 ())
 | effect Foo46 k -> 
 continue k (fun () -> if true then perform Foo93() else perform Foo94 ())
 | effect Foo47 k -> 
 continue k (fun () -> if true then perform Foo95() else perform Foo96 ())
 | effect Foo48 k -> 
 continue k (fun () -> if true then perform Foo97() else perform Foo98 ())
 | effect Foo49 k -> 
 continue k (fun () -> if true then perform Foo99() else perform Foo100 ())
 | effect Foo50 k -> 
 continue k (fun () -> if true then perform Foo101() else perform Foo102 ())
 | effect Foo51 k -> 
 continue k (fun () -> if true then perform Foo103() else perform Foo104 ())
 | effect Foo52 k -> 
 continue k (fun () -> if true then perform Foo105() else perform Foo106 ())
 | effect Foo53 k -> 
 continue k (fun () -> if true then perform Foo107() else perform Foo108 ())
 | effect Foo54 k -> 
 continue k (fun () -> if true then perform Foo109() else perform Foo110 ())
 | effect Foo55 k -> 
 continue k (fun () -> if true then perform Foo111() else perform Foo112 ())
 | effect Foo56 k -> 
 continue k (fun () -> if true then perform Foo113() else perform Foo114 ())
 | effect Foo57 k -> 
 continue k (fun () -> if true then perform Foo115() else perform Foo116 ())
 | effect Foo58 k -> 
 continue k (fun () -> if true then perform Foo117() else perform Foo118 ())
 | effect Foo59 k -> 
 continue k (fun () -> if true then perform Foo119() else perform Foo120 ())
 | effect Foo60 k -> 
 continue k (fun () -> if true then perform Foo121() else perform Foo122 ())
 | effect Foo61 k -> 
 continue k (fun () -> if true then perform Foo123() else perform Foo124 ())
 | effect Foo62 k -> 
 continue k (fun () -> if true then perform Foo125() else perform Foo126 ())
 | effect Foo63 k ->  continue k (fun () -> ())
 | effect Foo64 k ->  continue k (fun () -> ())
 | effect Foo65 k ->  continue k (fun () -> ())
 | effect Foo66 k ->  continue k (fun () -> ())
 | effect Foo67 k ->  continue k (fun () -> ())
 | effect Foo68 k ->  continue k (fun () -> ())
 | effect Foo69 k ->  continue k (fun () -> ())
 | effect Foo70 k ->  continue k (fun () -> ())
 | effect Foo71 k ->  continue k (fun () -> ())
 | effect Foo72 k ->  continue k (fun () -> ())
 | effect Foo73 k ->  continue k (fun () -> ())
 | effect Foo74 k ->  continue k (fun () -> ())
 | effect Foo75 k ->  continue k (fun () -> ())
 | effect Foo76 k ->  continue k (fun () -> ())
 | effect Foo77 k ->  continue k (fun () -> ())
 | effect Foo78 k ->  continue k (fun () -> ())
 | effect Foo79 k ->  continue k (fun () -> ())
 | effect Foo80 k ->  continue k (fun () -> ())
 | effect Foo81 k ->  continue k (fun () -> ())
 | effect Foo82 k ->  continue k (fun () -> ())
 | effect Foo83 k ->  continue k (fun () -> ())
 | effect Foo84 k ->  continue k (fun () -> ())
 | effect Foo85 k ->  continue k (fun () -> ())
 | effect Foo86 k ->  continue k (fun () -> ())
 | effect Foo87 k ->  continue k (fun () -> ())
 | effect Foo88 k ->  continue k (fun () -> ())
 | effect Foo89 k ->  continue k (fun () -> ())
 | effect Foo90 k ->  continue k (fun () -> ())
 | effect Foo91 k ->  continue k (fun () -> ())
 | effect Foo92 k ->  continue k (fun () -> ())
 | effect Foo93 k ->  continue k (fun () -> ())
 | effect Foo94 k ->  continue k (fun () -> ())
 | effect Foo95 k ->  continue k (fun () -> ())
 | effect Foo96 k ->  continue k (fun () -> ())
 | effect Foo97 k ->  continue k (fun () -> ())
 | effect Foo98 k ->  continue k (fun () -> ())
 | effect Foo99 k ->  continue k (fun () -> ())
 | effect Foo100 k ->  continue k (fun () -> ())
 | effect Foo101 k ->  continue k (fun () -> ())
 | effect Foo102 k ->  continue k (fun () -> ())
 | effect Foo103 k ->  continue k (fun () -> ())
 | effect Foo104 k ->  continue k (fun () -> ())
 | effect Foo105 k ->  continue k (fun () -> ())
 | effect Foo106 k ->  continue k (fun () -> ())
 | effect Foo107 k ->  continue k (fun () -> ())
 | effect Foo108 k ->  continue k (fun () -> ())
 | effect Foo109 k ->  continue k (fun () -> ())
 | effect Foo110 k ->  continue k (fun () -> ())
 | effect Foo111 k ->  continue k (fun () -> ())
 | effect Foo112 k ->  continue k (fun () -> ())
 | effect Foo113 k ->  continue k (fun () -> ())
 | effect Foo114 k ->  continue k (fun () -> ())
 | effect Foo115 k ->  continue k (fun () -> ())
 | effect Foo116 k ->  continue k (fun () -> ())
 | effect Foo117 k ->  continue k (fun () -> ())
 | effect Foo118 k ->  continue k (fun () -> ())
 | effect Foo119 k ->  continue k (fun () -> ())
 | effect Foo120 k ->  continue k (fun () -> ())
 | effect Foo121 k ->  continue k (fun () -> ())
 | effect Foo122 k ->  continue k (fun () -> ())
 | effect Foo123 k ->  continue k (fun () -> ())
 | effect Foo124 k ->  continue k (fun () -> ())
 | effect Foo125 k ->  continue k (fun () -> ())
 | effect Foo126 k ->  continue k (fun () -> ())