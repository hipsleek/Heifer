
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
(*@  ensures  (true, Foo.Goo, ()) @*)
= 
  match f () with 
  | x -> perform Done 
  | effect Foo k -> continue k (fun () -> ())
  | effect Goo k -> ()
