
effect Foo : (unit -> unit)
effect Goo : (unit -> unit)
effect Foo1 : (unit -> unit)
effect Goo1 : (unit -> unit)


let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo!).(Goo!).(Foo1!).(Goo1!).Goo?().Foo?().Foo1?().Goo1?(), ()) @*)
(*@  ensures  (true, (Foo!).(Goo!).(Foo1!).(Goo1!).Goo?().Foo?().Foo1?()._, ()) @*)
(*@  ensures  (true, ((Foo!).(Goo!).(Foo1!).(Goo1!).Goo?().Foo?().Foo1?().Goo1?())^*, ()) @*)

(*@  ensures  (true, (Foo!).Goo?().Foo?(), ()) @*)
(*@  ensures  (true, (Foo!).(Goo!).Goo?(), ()) @*)
(*@  ensures  (true, (_)^w, ()) @*)

= 
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
(*@  ensures  (true, (Foo.Goo.Foo1.Goo1), ()) @*)
(*@  ensures  (true, (Foo.Goo.Foo1.Goo1)^*, ()) @*)
(*@  ensures  (true, (Goo), ()) @*)
(*@  ensures  (true, (Goo)^*, ()) @*)

= 
  match f () with 
  | x -> x
  | effect Foo k -> 
    continue k (fun () -> ())
  | effect Goo k -> 
    continue k (fun () -> ())
  | effect Foo1 k -> 
    continue k (fun () -> ())
  | effect Goo1 k -> 
    continue k (fun () -> ())

   