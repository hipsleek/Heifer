effect Foo : (unit -> unit)
exception Goo of unit

let foo0 () = 
  perform Foo (print_string ("I am the augument\n"))

let goo () = 
  raise (Goo (print_string ("I am the exn augument\n")))


let foo1 () = (print_string ("Foo1\n"); perform Foo ())


let foo2 () = (print_string ("Foo2\n"); perform Foo ())


let f _ _ =  
  print_string ("Start\n");;

let main = 
  let a = f (print_string "hshhshs\n")  in 
  a (print_string "lalla\n")


(*let main1 = 
  match foo0 () with 
  | x -> x
  | effect Foo k -> (print_string ("I am the handler\n"); continue k (fun () -> ())) 

let main = 
  match goo () with 
  | x -> x
  | exception Goo _ -> (print_string ("I am the exception handler\n");) 
*)