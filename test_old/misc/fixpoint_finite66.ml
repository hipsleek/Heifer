

effect Foo : (unit -> unit)
effect Goo : (unit -> unit)
effect Koo : (unit -> unit)
effect Zoo : (unit -> unit)
effect Hoo : (unit -> unit)
effect Done : (unit -> unit)

let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()).Goo.Q(Goo()) @*)
  = print_string ("Foo\n");
    perform Foo ();
<<<<<<< HEAD
    perform Foo ()



let res11 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo^* @*)
  =
  match f () with
  | _ -> perform Goo ()
  | effect Foo k ->  continue k (fun () -> ()) 
=======
    print_string ("Goo\n");
    perform Goo ()


let res12 ()
  (*@ requires _^* @*)
  (*@ ensures Foo.Koo.Q(Koo()).Goo.Goo.Zoo.Q(Zoo()).Done  @*)
  =
  match f () with
  | _ -> print_string ("Done\n"); perform Done  ()
  | effect Foo k ->  
    print_string ("Koo\n"); perform Koo (); 
    continue (Obj.clone_continuation k) (fun () -> 
        print_string ("Goo\n"); perform Goo ()); 
    print_string ("Zoo\n"); perform Zoo ();
    (*continue k (fun () -> ()); 
    print_string ("Hoo\n"); perform Hoo ();*)
  | effect Goo k -> print_string ("H_G\n"); continue k (fun () -> ()); print_string ("POST_G\n")

let main = 
  match res12 () with 
  | _ -> ()
  | effect Koo k -> print_string ("H_K\n"); continue k  (fun () -> ())
  | effect Zoo k -> print_string ("H_Z\n");continue k  (fun () -> ())
  | effect Done k -> print_string ("H_DONE\n"); continue k  (fun () -> ())
  | effect Hoo k -> print_string ("H_H\n"); continue k  (fun () -> ())
>>>>>>> 86d40455527021690af7340f1d56fed9a4a908fe
