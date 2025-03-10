type _ eff += Fork  : (unit -> unit) -> unit eff
type _ eff += Yield : unit eff

let fork f = perform (Fork f)
let yield () = perform Yield

(* A concurrent round-robin scheduler *)
let run main =
  let run_q = Queue.create () in
  let enqueue k = Queue.push k run_q in
  let dequeue () =
    if Queue.is_empty run_q then () else continue (Queue.pop run_q) ()
  in
  let rec spawn f =
    (* Effect handler => instantiates fiber *)
    match f () with
    | () -> dequeue ()
    | exception e ->
        ( print_string (Printexc.to_string e);
          dequeue () )
    | effect Yield k ->
        ( enqueue k; dequeue () )
    | effect (Fork f) k ->
        ( enqueue k; spawn f )
  in
  spawn main

let main () =
  let task name () =
    Printf.printf "starting %s\n%!" name;
    Printf.printf "yielding %s\n%!" name;
    yield ();
    Printf.printf "ending %s\n%!" name;
    ()
  in 
  let pa = fork (task "a") in
  let _pb = fork (task "b") in
  let _pc = fork (task "c") in
  let _pe = fork (task "d") in
  let _pd = fork (task "e") in
  
  let p_total = (yield ();fork (fun () -> fork (task "a"); fork (task "b") )) in
  p_total

let _ = run main