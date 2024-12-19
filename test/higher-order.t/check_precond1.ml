
effect A : unit

let rec f ()
  (*@ requires (_^* ). A @*)
  (*@ ensures A @*)
=
  perform A


let middle ()
  (*@ requires (_^* ) @*)
  (*@ ensures A.A @*)
=
  perform A;
  match f () with
  | x -> x
  | effect A k -> continue k ()

let main 
  (*@ requires (_^* ) @*)
  (*@ ensures A.A @*)
= 
  match middle () with 
  | _ -> ()
  | effect A k -> continue k ()
