
effect Get : int
effect Put : int -> unit

let get ()
  (*@ requires emp @*)
  (*@ ensures Get @*)
= perform Get

let put s
  (*@ requires Get @*)
  (*@ ensures Put @*)
= perform (Put s)

let f ()
  (*@ requires emp @*)
  (*@ ensures Get.Put @*)
=
  let a = get () in
  put (a  + 1 );
  a  + 2 

  (* 
  1. always read after set  Put.(Put|Get)*
  2. the reset can not happend from the begeining. 
  3. can only decrease when the counter is positive. 
  4. trace with value, can prove the value of counter >=0 
      -> implies termination. 
  5. file protocal, can only read when opened. 
  ... 
  connection with monad. 

  *)

let main  () =
  let g =
    match f () with
    | r -> fun s -> (s, r)
    | effect (Put s1) k ->
      fun _ -> continue k () s1
    | effect Get k ->
      fun s -> continue k s s
  in g 1

let () =
  let s, r = main () in
  Format.printf "state %d res %d@." s r

