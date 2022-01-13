

effect Wait : (int -> unit)
effect Ready : (unit)

let send n 
(*@ requires _^* @*)
(*@ ensures Waist.Q(Wait ()) @*)
= 
  let a = perform Wait in 
  a n

let server n
(*@ requires _^* @*)
(*@ ensures  (Wait ^* ) @*)
= match send n with
| _ -> perform Ready
| effect Wait k -> continue k (fun i -> if i = 0 then () else send (i-1))

let main = server (-10)


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
