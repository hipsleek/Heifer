
effect Exc : (unit -> unit)
effect Other : (unit -> unit)

let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Exc!).(Other!).Other?().Exc?(), ()) @*)
= 
  let x = perform Exc in 
  let y = perform Other in 
  y ();
  x ()

let handler 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, Exc.Other, ()) @*)
= 
  match f () with 
  | x -> perform Done 
  | effect Exc k -> continue k (fun () -> ())
  | effect Other k -> ()
