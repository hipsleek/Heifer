
effect Foo : (unit -> unit)
effect Goo : (unit -> unit)
effect Foo1 : (unit -> unit)
effect Goo1 : (unit -> unit)
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


let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo!).(Goo!).(Foo1!).
   (Goo1!).(Foo!).(Goo!).(Foo1!).
   (Goo1!).(Foo2!).(Foo3!).(Foo4!).
   (Foo5!).(Foo6!).(Foo7!).(Foo8!).
   (Foo9!).(Foo10!).(Foo11!).
   (Foo12!).(Foo13!).Goo?().
   Foo?().Foo1?().Goo1?().Goo?().
   Foo?().Foo1?().Goo1?().Foo2?().
   Foo3?().Foo4?().Foo5?().Foo6?().
   Foo7?().Foo8?().Foo9?().Foo10?().
   Foo11?().Foo12?().Foo13?(), ()) @*)

(*@  ensures  (true, ((Foo!).(Goo!).(Foo1!).
   (Goo1!).(Foo!).(Goo!).(Foo1!).
   (Goo1!).(Foo2!).(Foo3!).(Foo4!).
   (Foo5!).(Foo6!).(Foo7!).(Foo8!).
   (Foo9!).(Foo10!).(Foo11!).
   (Foo12!).(Foo13!).Goo?().
   Foo?().Foo1?().Goo1?().Goo?().
   Foo?().Foo1?().Goo1?().Foo2?().
   Foo3?().Foo4?().Foo5?().Foo6?().
   Foo7?().Foo8?().Foo9?().Foo10?().
   Foo11?().Foo12?().Foo13?())^*, ()) @*)


(*@  ensures  (true, (Foo!).(Goo!).(Foo1!).(Goo1!).Goo?().Foo?().Foo1?()._, ()) @*)
(*@  ensures  (true, ((Foo!).(Goo!).(Foo1!).(Goo1!).Goo?().Foo?().Foo1?().Goo1?())^*, ()) @*)
(*@  ensures  (true, (Foo!)._, ()) @*)

(*@  ensures  (true, (_)^oo, ()) @*)
(*@  ensures  (true, (Foo!).(Goo!).Goo?(), ()) @*)
(*@  ensures  (true, (_)^*, ()) @*)

= 
  let x = perform Foo in 
  let y = perform Goo in 
  let xx = perform Foo1 in 
  let yy = perform Goo1 in 
  let xs = perform Foo in 
  let ys = perform Goo in 
  let xxs = perform Foo1 in 
  let yys = perform Goo1 in 
  let a2 = perform Foo2 in 
  let a3 = perform Foo3 in 
  let a4 = perform Foo4 in 
  let a5 = perform Foo5 in 
  let a6 = perform Foo6 in 
  let a7 = perform Foo7 in 
  let a8 = perform Foo8 in 
  let a9 = perform Foo9 in 
  let a10 = perform Foo10 in 
  let a11 = perform Foo11 in 
  let a12 = perform Foo12 in 
  let a13 = perform Foo13 in 

  y ();
  x ();
  xx ();
  yy ();
  y ();
  x ();
  xx ();
  yy ();
  a2();
  a3();
  a4();
  a5();
  a6();
  a7();
  a8();
  a9();
  a10();
  a11();
  a12();
  a13()


let handler 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, Foo.Goo.Foo1.Goo1.Foo.Goo.Foo1.Goo1.Foo2.Foo3.Foo4.Foo5.Foo6.Foo7.Foo8.Foo9.Foo10.Foo11.Foo12.Foo13.(Done!).(AftGoo1!).(AftFoo1!).(AftGoo!).(AftFoo!).(AftGoo1!).(AftFoo1!).(AftGoo!).(AftFoo!), ()) @*)
(*@  ensures  (true, (Foo.Goo.Foo1.Goo1.Foo.Goo.Foo1.Goo1.Foo2.Foo3.Foo4.Foo5.Foo6.Foo7.Foo8.Foo9.Foo10.Foo11.Foo12.Foo13.(Done!).(AftGoo1!).(AftFoo1!).(AftGoo!).(AftFoo!).(AftGoo1!).(AftFoo1!).(AftGoo!).(AftFoo!))^*, ()) @*)


(*@  ensures  (true, Foo6.Foo7.Foo8.Foo9.Foo10.Foo11.Foo12.Foo13.(Done!).(AftGoo1!).(AftFoo1!).(AftGoo!).(AftFoo!).(AftGoo1!).(AftFoo1!).(AftGoo!).(AftFoo!), ()) @*)

(*@  ensures  (true, (Foo.Goo.Foo1.Goo1)^*, ()) @*)
(*@  ensures  (true, (Goo), ()) @*)
(*@  ensures  (true, (_)^*, ()) @*)

= 
  match f () with 
  | x -> 
    perform Done

  | effect Foo k -> 
    continue k 
    (fun () -> ());
    perform AftFoo

  | effect Goo k -> 
    continue k 
    (fun () -> ());
    perform AftGoo

  | effect Foo1 k -> 
    continue k 
    (fun () -> ());
    perform AftFoo1

  | effect Goo1 k -> 
    continue k 
    (fun () -> ());

    perform AftGoo1


   | effect Foo2 k ->  
    continue k 
   (fun () -> ());

 | effect Foo3 k ->  
  continue k 
 (fun () -> ());

 | effect Foo4 k ->  
  continue k 
    (fun () -> ());

 | effect Foo5 k ->  
  continue k 
    (fun () -> ());

 | effect Foo6 k ->  
  continue k 
    (fun () -> ());

 | effect Foo7 k ->  
  continue k 
    (fun () -> ());

 | effect Foo8 k ->  
  continue k 
    (fun () -> ());

 | effect Foo9 k ->  
  continue k 
    (fun () -> ());

 | effect Foo10 k -> 
  continue k 
    (fun () -> ());

 | effect Foo11 k ->  
  continue k 
    (fun () -> ());

 | effect Foo12 k ->  
  continue k 
    (fun () -> ());

 | effect Foo13 k ->  
  continue k 
    (fun () -> ());

 | effect Foo14 k ->  
  continue k 
    (fun () -> ());
    
 | effect Foo15 k -> 
  continue k 
    (fun () -> ());
    