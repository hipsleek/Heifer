
effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo!).(Goo!).Goo?().Foo?(), ()) @*)
(*@  ensures  (true, (Foo!).(Goo!).Goo?()._, ()) @*)
(*@  ensures  (true, ((Foo!).(Goo!).Goo?()._)^*, ()) @*)

(*@  ensures  (true, (Foo!).Goo?().Foo?(), ()) @*)
(*@  ensures  (true, (Foo!).(Goo!).Goo?(), ()) @*)
(*@  ensures  (true, (_)^w, ()) @*)

= 
  let x = perform Foo in 
  let y = perform Goo in 
  y ();
  x ()

let handler 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo), ()) @*)
(*@  ensures  (true, (Foo)^*, ()) @*)
(*@  ensures  (true, (Goo), ()) @*)
(*@  ensures  (true, (Goo)^*, ()) @*)

= 
  match f () with 
  | x -> x
  | effect Foo k -> () 
