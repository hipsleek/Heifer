

effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Goo.Q(Foo()).Q(Goo()) @*)
  = let a = perform Foo in 
    let b = perform Goo in 
    b (); a ()


(*
let f1 () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo 1).Foo.Q(Foo()) @*)
  = print_string ("Foo\n");
    perform Foo ();
    perform Foo ()

let res11 () 
  (*@ requires _^* @*)
  (*@ ensures  Foo^* @*)
  =
  match f1 () with
  | _ -> ()
  | effect Foo k ->  continue k (fun () -> perform Foo ())
*)
