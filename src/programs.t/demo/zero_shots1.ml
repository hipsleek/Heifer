
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

let store = ref 0;

let f () = 
  store := store + 1;
  let x = perform (Foo) in 
  store := store + 1;
  let x2 = perform (Foo) in 
  x2 ();
  x () 


let h () = 
  match f () with 
  |_ -> ()
  | effect (Foo) k -> continue k (fun () -> !store)