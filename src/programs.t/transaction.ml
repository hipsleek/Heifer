
(* the ref to update transactionally, and the value to update it with *)
effect Update : int ref * int -> unit

let r = ref 0

let atomically f 
(*@ requires _^* , eff(f)= _^* ->  (Update^* ) @*)
(*@ ensures  (Update^* ).(Res \/ emp) @*)
=
  let comp =
    match f () with
    | x -> (fun _ -> x)
    | effect (Update (r,v)) k -> (fun rb ->
        let old_v = !r in
        r := v;
        continue k () (fun () -> r := old_v; rb ()))
  in comp (fun () -> ())



let (:=) r v
  (*@ requires _^* @*)
  (*@ ensures Update @*)
= perform (Update (r,v))


let g ()
  (*@ requires _^*  @*)
  (*@ ensures Update.Update.Update @*)
=
  r := 20;
  r := 21;
  r := 30

let h () 
  (*@ requires emp @*)
  (*@ ensures emp @*)
=
  atomically g
  
