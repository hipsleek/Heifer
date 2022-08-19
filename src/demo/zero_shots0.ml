
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
(*@  ensures  (true, (Exc), ()) @*)
= 
  match f () with 
  | x -> x
  | effect Exc k -> () 
