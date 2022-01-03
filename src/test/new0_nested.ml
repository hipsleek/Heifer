
effect Foo : string
effect Goo : string

let performFoo () =
  print_string ("Foo\n");
  let str = perform Foo  in 
  print_string (str  ^ "done Foo\n") 

let performGoo () =
  print_string ("Goo\n");
  let str = perform Goo in 
  print_string (str  ^ "done Goo\n") 

let f () =
  performFoo ()
  

let handlerInner () =
  match f () with 
  | n -> n
  | effect Foo k -> (performGoo (); continue k ("performing Foo...\n"))


let handlerOutter=
  match handlerInner () with 
  | n -> n
  | effect Goo k -> continue k ("performing Goo...\n")

