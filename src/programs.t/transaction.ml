
(* the ref to update transactionally, and the value to update it with *)
effect Update : int ref * int -> unit


let atomically f 
(*@ requires _^* , eff(f)= _^* ->  (Update^* ) @*)
(*@ ensures  (U^* ).(Res \/ emp) @*)
=
  let comp =
    match f () with
    | x -> (fun _ -> x)
    | exception e -> (fun rb -> rb (); raise e)
    | effect (Update (r,v)) k -> (fun rb ->
        let old_v = !r in
        r := v;
        continue k () (fun () -> r := old_v; rb ()))
  in comp (fun () -> ())



let ref = ref
let (!) 
(*@ requires _^* @*)
  (*@ ensures emp @*)
= (!)

let (:=) r v
  (*@ requires _^* @*)
  (*@ ensures Update @*)
= perform (Update (r,v))

exception Res of int

let g ()
  (*@ requires _^*  @*)
  (*@ ensures Update.Update.Update @*)
=
  r := 20;
  r := 21;
  printf "T1: Before abort %d\n" (!r);
  raise (Res !r) |> ignore;
  printf "T1: After abort %d\n" (!r);
  r := 30

let h () 
  (*@ requires emp @*)
  (*@ ensures emp @*)
=
  atomically g
  
(*
let f () = atomically h

let () = f ()
*)