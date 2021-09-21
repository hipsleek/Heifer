effect Foo : (unit -> unit)

let foo1 () = (print_string ("Foo1\n"); perform Foo ())


let foo2 () = (print_string ("Foo2\n"); perform Foo ())


let f _ _ =  
  print_string ("Start\n");;


let main = 
  f (foo1 ()) (foo2 ())  

