
(* the ref to update transactionally, and the value to update it with *)
effect Update : int ref * int -> unit

let atomically f =
(* requires emp /\ Eff(f()) = U^*.(Res \/ emp)
   ensures  U^*.(Res \/ emp) *)
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
let (!) = (!)
let (:=) r v
= perform (Update (r,v))

exception Res of int

let () = atomically (fun () ->
  let r = ref 10 in
  printf "T0: %d\n" (!r);
  try atomically (fun () ->
    r := 20;
    r := 21;
    printf "T1: Before abort %d\n" (!r);
    raise (Res !r) |> ignore;
    printf "T1: After abort %d\n" (!r);
    r := 30)
  with
  | Res v -> Printf.printf "T0: T1 aborted with %d\n" v;printf "T0: %d\n" !r)
