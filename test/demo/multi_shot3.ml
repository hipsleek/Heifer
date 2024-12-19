
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
(*@  ensures  (true, Foo.(BefFoo!).Goo.(BefGoo!).(AftDone!).(AftGoo!).Goo.(BefGoo!).(AftDone!).(AftGoo!).(AftFoo!), ()) @*)
= 
  match f () with 
  | x -> perform AftDone
  | effect Foo k -> perform BefFoo; continue k (fun () -> ()); continue k (fun () -> ()) ; perform AftFoo
  | effect Goo k -> perform BefGoo; continue k (fun () -> ()); perform AftGoo;
