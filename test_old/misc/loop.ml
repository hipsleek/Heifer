
effect Foo : (unit -> unit)

let f () = perform Foo () 

let loop 
= match f () with
| _ -> ()
| effect Foo k -> continue k 
	(fun () -> perform Foo ())
