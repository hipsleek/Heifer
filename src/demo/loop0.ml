
effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo!).Foo?(), ()) @*)
= 
  let x = perform Foo in 
  x ()

let handler 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, Foo^w, ()) @*)
= 
  match f () with 
  | x -> x
  | effect Foo k -> continue k (fun () -> perform Foo )
  | effect Goo k -> () 

(*
  (Foo!).Foo?()
   his         current ev        continuation (k)           bindings 
1  emp          (Foo!)          Foo?()                   Foo? = (fun () -> perform Foo )
2  Foo          Foo?()         emp 
*  Foo?()   -> Foo! Foo?()
3. Foo.(FOo)W


----------------------------------

*)