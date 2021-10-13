
(* the ref to update transactionally, and the value to update it with *)

effect Exc : int -> unit

let raise n
  (*@ requires _^* @*)
  (*@ ensures Exc @*)
= perform (Exc n);

effect Update : int ref * int -> unit

let r = ref 0

let atomically f 
(*@ requires _^* , eff(f)= ((~Exc)^* ) ->  (Update^* ).(Exc \/ emp) @*)
(*@ ensures  (Update^* ).(Exc \/ emp) @*)
=
  let comp =
    match f () with
    | x -> (fun _ -> x)
    | effect (Exc _) k -> (fun rb -> rb ())
    | effect (Update (r,v)) k -> (fun rb ->
        let old_v = !r in
        r := v;
        continue k () (fun () -> r := old_v; rb ()))
  in comp (fun () -> ())

let (:=) r v
  (*@ requires _^* @*)
  (*@ ensures Update @*)
= perform (Update (r,v))


let error ()
  (*@ requires _^*  @*)
  (*@ ensures Update.Update.Exc @*)
=
  r := 20;
  r := 21;
  raise 404;
  r := 30

let g ()
  (*@ requires _^*  @*)
  (*@ ensures Update.Update.Update @*)
=
  r := 20;
  r := 21;
  r := 300

let h 
  (*@ requires emp @*)
  (*@ ensures _^* @*)
=
  atomically error

 


  
