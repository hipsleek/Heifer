
effect Foo : (int -> unit)


let f2 _ () = 
  (* Foo. Q (Foo(5)) *)
  (print_string ("Foo\n") ; 
  perform Foo 5; 
  (* (fun n -> ()) 5 *)
  print_string ("Foo1\n") )


let f n = 
  (* Foo. Q (Foo(5)) *)
  f2 n 

let main = 
  match f (1) with 
  (* Foo. Q (Foo(5)) *)
  (* Foo. emp *)
  (* Foo *)
  | _ -> ()
  | effect Foo k -> 
    (continue k (fun n -> ()); 
    print_string ("song\n");
    (continue (Obj.clone_continuation k) (fun n -> ()))
    )

