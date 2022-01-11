effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()).Foo.Q(Foo()) @*)
  = print_string ("Foo\n");
    perform Foo ();
    print_string ("Foo\n");
    perform Foo ()

let res1 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> ())

let res11 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Goo.Q(Goo()).Goo.Q(Goo()) @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> ()); print_string ("Goo\n"); perform Goo ()


let handler11 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Goo.Goo @*)
  = 
  match res11 () with 
  | _ -> ()
  | effect Goo k -> continue k (fun () -> ())


let res2 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  ()


let res3 ()
  (*@ requires _^* @*)
  (*@ ensures  (Foo).(Goo).Q(Goo ()).(Foo).(Goo).Q(Goo ()) @*)
  
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  print_string ("Goo\n"); perform Goo (); continue k (fun () -> ())

let handler3 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Goo.Foo.Goo @*)
  = 
  match res3 () with 
  | _ -> ()
  | effect Goo k -> continue k (fun () -> ())




let res4 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Goo.Q(Goo()) @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  print_string ("Goo\n"); perform Goo (); ()


let res41 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Goo.Q(Goo()).Foo.Goo.Q(Goo()) @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  print_string ("Goo\n"); perform Goo (); continue k (fun () -> ())

let handler4 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Goo @*)
  = 
  match res4 () with 
  | _ -> ()
  | effect Goo k -> continue k (fun () -> ())

  
let handler41 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Goo.Foo.Goo @*)
  = 
  match res41 () with 
  | _ -> ()
  | effect Goo k -> continue k (fun () -> ())

let handler411 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Goo @*)
  = 
  match res41 () with 
  | _ -> ()
  | effect Goo k -> ()

let res11 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo^* @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> perfrom Goo ())



let res5 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Foo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  (continue (Obj.clone_continuation k) (fun () -> ())); 
                     continue k (fun () -> ())


(*

let main = 
  handler11 ()  
*)