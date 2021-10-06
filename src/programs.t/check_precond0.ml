
effect A : unit
effect B : unit

let rec f ()
  (*@ requires A @*)
  (*@ ensures B @*)
=
  perform B


let middle ()
  (*@ requires emp @*)
  (*@ ensures A.B @*)
=
  perform A;
  match f () with
  | x -> x
  | effect A k -> continue k ()

let main 
  (*@ requires emp @*)
  (*@ ensures A.B @*)
= 
  match middle () with 
  | _ -> ()
  | effect A k -> continue k ()
