
effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo!).(Goo!).Goo?().Foo?(), ()) @*)
= 
  let x = perform Foo in 
  let y = perform Goo in 
  y ();
  x ()

let handler 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, Foo.Goo.Goo, ()) @*)
= 
  match f () with 
  | x -> x
  | effect Foo k -> continue k (fun () -> perform Goo ())
  | effect Goo k -> continue k (fun () -> ())
