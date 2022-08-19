
effect Foo : (unit -> unit)
effect AftFoo : (unit -> unit)

effect Goo : (unit -> unit)
effect AftGoo : (unit -> unit)

effect Foo1 : (unit -> unit)
effect AftFoo1 : (unit -> unit)

effect Goo1 : (unit -> unit)
effect AftGoo1 : (unit -> unit)

effect Before : (unit -> unit)

effect Done : (unit -> unit)

effect Goo : (unit -> unit)
effect Foo1 : (unit -> unit)

effect Goo1 : (unit -> unit)
effect Foo0 : (unit -> unit)
effect Foo1 : (unit -> unit)
effect Foo2 : (unit -> unit)
effect Foo3 : (unit -> unit)
effect Foo4 : (unit -> unit)
effect Foo5 : (unit -> unit)



let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo!).(Goo!).(Foo1!).
   (Goo1!).(Foo!).(Goo!).(Foo1!).(Goo1!).
   (Foo2!).(Foo3!).(Foo4!).(Foo5!).
   (Foo6!).(Foo7!).Goo?().Foo?().
   Foo1?().Goo1?().Goo?().Foo?().
   Foo1?().Goo1?().Foo2?().Foo3?().
   Foo4?().Foo5?().Foo6?().Foo7?(), 
   ()) @*)

(*@  ensures  (true, (Foo!).(Goo!).
   (Foo1!).(Goo1!).(Foo!).(Goo!).(Foo1!).(Goo1!).
   (Foo2!).(Foo3!).(Foo4!).Goo?().Foo?().Foo1?().Goo1?().Goo?().Foo?().
   Foo1?().Goo1?().Foo2?().Foo3?().Foo4?(), ()) \/ (true/\true, (Foo!).(Goo!).
   (Foo1!).(Goo1!).(Foo!).(Goo!).(Foo1!).(Goo1!).(Foo2!).(Foo3!).(Foo4!).Goo?().Foo?().Foo1?().
   Goo1?().Goo?().Foo?().Foo1?().Goo1?().Foo2?().Foo3?().Foo4?(), ()) @*)

(*@  ensures  (true, ((Foo!).(Goo!).(Foo1!).
   (Goo1!).(Foo!).(Goo!).(Foo1!).(Goo1!).
   (Foo2!).(Foo3!).(Foo4!).(Foo5!).
   (Foo6!).(Foo7!).Goo?().Foo?().
   Foo1?().Goo1?().Goo?().Foo?().
   Foo1?().Goo1?().Foo2?().Foo3?().
   Foo4?().Foo5?().Foo6?()._)^*, 
   ()) @*)

(*@  ensures  (true, _.(Goo!).(Foo1!).
   (Goo1!).(Foo!).(Goo!).(Foo1!).(Goo1!).
   (Foo2!).(Foo3!).(Foo4!).(Foo5!).
   (Foo6!).(Foo7!).Goo?().Foo?().
   Foo1?().Goo1?().Goo?()._.
   Foo1?().Goo1?().Foo2?().Foo3?().
   Foo4?().Foo5?().Foo6?()._, 
   ()) @*)

(*@  ensures  (true, (_)^*, ()) @*)

(*@  ensures  (true, (Foo!).Goo?().Foo?(), ()) @*)
(*@  ensures  (true, (Foo!).(Goo!).Goo?(), ()) @*)
(*@  ensures  (true, (_)^w, ()) @*)

= 
  if x then 
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
  a4()

else 

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
  a5()



let handler ()
(*@  requires (true, emp, ())   @*)

(*@ ensures  (true, Foo.(Before!).Goo.Foo1.Goo1.
   (Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).
   Foo2.Foo3.Foo4.(Before!).Foo5.(Before!).Foo6.(Before!).
   Foo7.(Before!).(Done!).(Done!).(Done!).(Done!).(Done!).
   (Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).
   (Done!).(AftFoo!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).
   (AftGoo!).(Done!).(AftFoo!).(Done!), ())@*)

(*@  ensures  (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true, Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.Foo4.(Before!).(Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) \/ (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true, Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.Foo4.(Before!).(Foo5!).(Foo6!).(Foo7!).Foo5?().Foo6?().Foo7?().(Done!).(Done!).(Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) @*)

(*@ ensures  (true, (Foo.(Before!).Goo.Foo1.Goo1.
   (Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).
   Foo2.Foo3.Foo4.(Before!).Foo5.(Before!).Foo6.(Before!).
   Foo7.(Before!).(Done!).(Done!).(Done!).(Done!).(Done!).
   (Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).
   (Done!).(AftFoo!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).
   (AftGoo!).(Done!).(AftFoo!).(Done!))^* \/ emp, ())@*)


(*@  ensures  (true, (Before!).(Before!).Foo.(Before!).
   Goo.Foo1.Goo1.(Before!).Foo.(Before!).
   Goo.Foo1.Goo1.(Before!).Foo2.Foo3.Foo4.
   (Before!).Foo5.(Before!).Foo6.(Before!).
   Foo7.(Before!).(Done!).(Done!).(Done!).
   (Done!).(Done!).(Done!).(Done!).(AftGoo1!).
   (Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).
   (AftFoo!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).
   (Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) 
   \/ 
   (true, (Before!).(Before!).Foo.(Before!).Goo.Foo1.
   Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).
   Foo2.Foo3.Foo4.(Before!).Foo5.(Before!).
   Foo6.(Before!).Foo7.(Before!).
   (Done!).(Done!).(Done!).(Done!).
   (Done!).(Done!).(Done!).(AftGoo1!).(Done!).
   (AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).
   (Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).
   (AftGoo!).(Done!).(AftFoo!).(Done!), ()) @*)

(*@  ensures  (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true,
    Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.Foo4.
    (Before!).(Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).
    (AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) \/
     (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true, 
     Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.
     Foo4.(Before!).(Foo5!).(Foo6!).(Foo7!).Foo5?().Foo6?().Foo7?().(Done!).(Done!).(Done!).
     (Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).(AftGoo1!).
     (Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) @*)

(*@  ensures  (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true,
    Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.Foo4.
    (Before!).(Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).
    (AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) \/
     (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true, 
     Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.
     Foo4.(Before!).(Foo5!).(Foo6!).(Foo7!).Foo5?().Foo6?().Foo7?().(Done!).(Done!).(Done!).
     (Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).(AftGoo1!).
     (Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) @*)


(*@  ensures  (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true,
    Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.Foo4.
    (Before!).(Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).
    (AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) \/
     (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true, 
     Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.
     Foo4.(Before!).(Foo5!).(Foo6!).(Foo7!).Foo5?().Foo6?().Foo7?().(Done!).(Done!).(Done!).
     (Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).(AftGoo1!).
     (Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) @*)

(*@  ensures  (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true,
    Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.Foo4.
    (Before!).(Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).
    (AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) \/
     (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true, 
     Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.
     Foo4.(Before!).(Foo5!).(Foo6!).(Foo7!).Foo5?().Foo6?().Foo7?().(Done!).(Done!).(Done!).
     (Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).(AftGoo1!).
     (Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) @*)

(*@  ensures  (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true,
    Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.Foo4.
    (Before!).(Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).
    (AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) \/
     (true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true/\true, 
     Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.Foo3.
     Foo4.(Before!).(Foo5!).(Foo6!).(Foo7!).Foo5?().Foo6?().Foo7?().(Done!).(Done!).(Done!).
     (Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).(AftGoo1!).
     (Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), ()) @*)


=   if o then  

 

  match f () with 
  | x -> 
    perform Done

  | effect Foo k -> 
    perform Before; 

    continue k 
    (fun () -> ());
    perform AftFoo;
    perform Done

  | effect Goo k -> 
    continue k 
    (fun () -> ());
    perform AftGoo;
    perform Done

  | effect Foo1 k -> 
    continue k 
    (fun () -> ());
    perform AftFoo1;
    perform Done

  | effect Goo1 k -> 
    perform Before; 

    continue k 
    (fun () -> ());

    perform AftGoo1;
    perform Done


   | effect Foo2 k ->  
    continue k 
   (fun () -> ());
   perform Done

 | effect Foo3 k ->  
  continue k 
 (fun () -> ());
 perform Done
 
 | effect Foo4 k ->  
  perform Before; 


 else 

    match f () with 
    | x -> 
      perform Done
  
    | effect Foo k -> 
      perform Before; 
  
      continue k 
      (fun () -> ());
      perform AftFoo;
      perform Done
  
    | effect Goo k -> 
      continue k 
      (fun () -> ());
      perform AftGoo;
      perform Done
  
    | effect Foo1 k -> 
      continue k 
      (fun () -> ());
      perform AftFoo1;
      perform Done
  
    | effect Goo1 k -> 
      perform Before; 
  
      continue k 
      (fun () -> ());
  
      perform AftGoo1;
      perform Done
  
  
     | effect Foo2 k ->  
      continue k 
     (fun () -> ());
     perform Done
  
   | effect Foo3 k ->  
    continue k 
   (fun () -> ());
   perform Done
   
   | effect Foo4 k ->  
    perform Before; 
  
    continue k 
      (fun () -> ());
      perform Done
  


      
let hahha 
(*@  requires (true, emp, ())   @*)
(*@ ensures (true/\true/\true, Foo.(Before!).Goo.Foo1.Goo1.
   (Before!).Foo.(Before!).Goo.Foo1.Goo1.(Before!).Foo2.
   Foo3.Foo4.(Before!).Foo5.(Before!).Foo6.(Before!).Foo7.(Before!).(Done!).(Done!).(Done!).(Done!).(Done!).(Done!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!).(AftGoo1!).(Done!).(AftFoo1!).(Done!).(AftGoo!).(Done!).(AftFoo!).(Done!), x)@*)

   = 
  match handler () with 
  | x -> x

  
  
  