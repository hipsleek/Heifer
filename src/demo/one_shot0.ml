
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
  | x -> x
  | effect Foo k -> continue k (fun () -> ())
  | effect Goo k -> continue k (fun () -> ())


(*
  (Foo!).(Goo!).Goo?().Foo?()
   his         current ev        continuation (k)           bindings 
1  emp          (Foo!)          (Goo!).Goo?().Foo?()        Foo?() = (fun () -> ())
2  Foo          (Goo!)          Goo?().Foo?()               Goo?() = (fun () -> ())
3  Foo.Goo      Goo?()          Foo?() 
4  Foo.Goo.emp   Foo?()         emp       
5  Foo.Goo.emp.emp  
----------------------------------
Foo.Goo

*)