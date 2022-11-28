
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
  | x -> perform Done; 6
  | effect Foo k -> continue k (fun () -> 2); continue k (fun () -> 4); 10
  | effect Goo k -> continue k (fun () -> 3)

(*  (Foo!).(Goo!).Goo?().Foo?()
   his                     current ev        continuation (k)           bindings 
1  emp                      (Foo!)          (Goo!).Goo?().Foo?().@           Foo_1?() = (fun () -> 2)
2  Foo                      (Goo!)          Goo?().Foo_1?().@. (Goo!).Goo?().Foo_2?().@   Foo_2?() = (fun () -> 4)
3  Foo.Goo                  Goo?()          Foo_1?().@. (Goo!).Goo?().Foo_2?() .@               Goo?() = (fun () -> 3)
4  Foo.Goo.emp               Foo_1?()        @. (Goo!).Goo?().Foo_2?()  .@       
5  Foo.Goo.emp.emp           @               ( Goo!).Goo?().Foo_2?().@  
6. Foo.Goo.emp.emp.Done!     (Goo!)          Goo?().Foo_2?()  .@ 
7. Foo.Goo.emp.emp.Done!.Goo   Goo?()        Foo_2?()  .@ 
7. Foo.Goo.emp.emp.Done!.Goo.emp    Foo_2?()      @ 
7. Foo.Goo.emp.emp.Done!.Goo.emp.emp     @       emp 
7. Foo.Goo.emp.emp.Done!.Goo.emp.emp.Done!    (finished)       emp 

...
Foo.Goo.Done!.Goo.Done!

----------------------------------
*)