

effect Foo : (unit -> unit)
effect Goo : (unit -> unit)


let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()).Foo.Q(Foo()) @*)
  = print_string ("Foo\n");
    perform Foo ();
    print_string ("Foo\n");
    perform Foo ()



let res11 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo^* @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> perform Foo ())

(*

let res5 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Foo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  (continue (Obj.clone_continuation k) (fun () -> ())); 
                     continue k (fun () -> ())

*)