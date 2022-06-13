
effect Foo : (unit -> int)
effect Goo : (unit -> int)

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
(*@  ensures  (true, Foo.Goo.(Done!).Goo.(Done!), 3) @*)
= 
  match f () with 
  | x -> perform Done 
  | effect Foo k -> continue k (fun () -> 2); continue k (fun () -> 4)
  | effect Goo k -> continue k (fun () -> 3)
