
effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true,  (Foo!).(Goo!).Goo?().Foo?().\heart, ()) @*)
= 
  print_string ("Foo\n");
  let x = perform Foo in
  print_string ("Goo\n");
  let y = perform Goo in 
  y ();
  x ()

let handler 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, Foo.(BefFoo!).Goo.(BefGoo!).(AftDone!).(AftGoo!).Goo.(BefGoo!).(AftDone!).(AftGoo!).(AftFoo!), ()) @*)
= 
  match f () with 
  | x -> print_string ("Done\n")
  | effect Foo k -> v 
    
    
    print_string ("BefFoo\n"); (continue (Obj.clone_continuation k) (fun () -> ())); continue k (fun () -> ()) ; 
  print_string ("AftFoo\n") 
  | effect Goo k -> print_string ("BefGoo\n"); continue k (fun () -> ()); 
  print_string ("AftGoo\n") 
