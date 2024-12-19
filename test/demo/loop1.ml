
effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, (Foo!).(Goo!).Foo?(), ()) @*)
= 
  let h = perform Foo in 
  let g = perform Goo in 

  h ()

let handler 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, Foo^w, ()) @*)
= 
  match f () with 
  | x -> x
  | effect Foo k -> continue k (fun () -> perform Goo )
  | effect Goo k -> continue k (fun () -> perform Foo )

(*

  (Foo!).Foo?()
   his         current ev        continuation (k)           bindings 
1  emp          (Foo!)          Foo?()                   Foo? = (fun () -> perform Goo )
2  Foo          Foo?()         emp 
*  Foo?()   -> Goo!. Goo?()
3. Foo            Goo!          Goo?()                Goo? = (fun () -> perform Foo )
4. Foo.Goo       Goo?() 
* Goo?()    -> Foo! Foo?()
5. Foo.Goo.(Foo.Goo)^W



A.B.C. (Foo!).Foo?()
his         current ev        continuation (k)           bindings 
1  A.B.          C            (Foo!).Foo?()                
2  A.B.C          Foo!          Foo?()                  Foo? = (fun () -> perform Goo; perform L ) 
3. A.B.C.Foo      Foo?()         emp       
*  Foo?()   -> Goo!. L! Goo?()
4. A.B.C.Foo      Goo!         L!. Goo?()           Goo? = (fun () -> perform Foo )
5. A.B.C.Foo.Goo     L!        Goo?()             Goo? = (fun () -> perform Foo )
5. A.B.C.Foo.Goo.L!  Goo?()        emp             Goo? = (fun () -> perform Foo )
* Goo?()   -> Foo!. Foo?()

A.B.C.Foo.Goo.L!.(Foo.Goo.L!)^W
*)