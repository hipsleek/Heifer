
effect Foo : (unit -> unit)
effect AftFoo : (unit -> unit)

effect Goo : (unit -> unit)
effect AftGoo : (unit -> unit)

effect Foo1 : (unit -> unit)
effect AftFoo1 : (unit -> unit)

effect Goo1 : (unit -> unit)
effect AftGoo1 : (unit -> unit)

effect Done : (unit -> unit)


let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo!).(Goo!).(Foo1!).(Goo1!).Goo?().
   Foo?().Foo1?().Goo1?(), ()) @*)
   
(*@  ensures  (true, (Foo!).(Goo!).(Foo1!).(Goo1!).Goo?().
   Foo?().Foo1?().Goo1?(), ()) 
   \/ 
   (true, (Foo!).(Goo!).(Foo1!).
   (Goo1!).Goo?().Foo?().Foo1?().Goo1?(), ()) @*)

(*@  ensures  (true, ((Foo!).(Goo!).(Foo1!).(Goo1!).
   Goo?().Foo?().Foo1?().Goo1?())^*, ()) @*)

(*@  ensures  (true, (Foo!).Goo?().Foo?(), ()) @*)
(*@  ensures  (true, (Foo!).(Goo!).Goo?(), ()) @*)
(*@  ensures  (true, (_)^w, ()) @*)

= 
  if x then 
  let x = perform Foo in 
  let y = perform Goo in 
  let xx = perform Foo1 in 
  let yy = perform Goo1 in 
  y ();
  x ();
  xx ();
  yy ()
  else
    let x = perform Foo in 
  let y = perform Goo in 
  let xx = perform Foo1 in 
  let yy = perform Goo1 in 
  y ();
  x ();
  xx ();
  yy ()



let handler 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, Foo.Goo.Foo1.Goo1.(Done!).(AftGoo1!).
   (AftFoo1!).(AftGoo!).(AftFoo!), ()) @*)
(*@  ensures  (true, (Foo.Goo.Foo1.Goo1.(Done!).(AftGoo1!).
   (AftFoo1!).(AftGoo!).(AftFoo!))^*, ()) @*)
(*@  ensures  (true, (Goo), ()) @*)
(*@  ensures  (true, (Goo)^*, ()) @*)

= 
  match f () with 
  | x -> 
    perform Done
  | effect Foo k -> 
    continue k 
    (fun () -> ());
    if y then
       perform AftFoo
    else 
      perform AftFoo

  | effect Goo k -> 
    continue k 
    (fun () -> ());
    if y then
      perform AftGoo
   else 
     perform AftGoo

  | effect Foo1 k -> 
    continue k 
    (fun () -> ());
    if y then
      perform AftFoo1
   else 
     perform AftFoo1


  | effect Goo1 k -> 
    continue k 
    (fun () -> ());
    if y then
      perform AftGoo1
   else 
     perform AftGoo1


    