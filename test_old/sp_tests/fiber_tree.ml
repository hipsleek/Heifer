(* Demonstrate the concurrent scheduler
  ------------------------------------
   Spawn binary tree of tasks in depth-first order

       ************
        Fiber tree
       ************
             0
           /  \
          1    2
         / \  / \
        3   4 5  6
*)
effect Fork  : (unit -> unit) -> unit
let fork f = perform (Fork f)

effect Yield : unit
let yield () = perform Yield

(* A concurrent round-robin scheduler *)
let run main =
  let run_q = Queue.create () in
  let enqueue k = Queue.push k run_q in
  let rec dequeue () =
    if Queue.is_empty run_q then ()
    else continue (Queue.pop run_q) ()
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

let log = Printf.printf

let rec f id depth =
  log "Starting number %i\n%!" id;
  if depth > 0 then begin
    log "Forking number %i\n%!" (id * 2 + 1);
    fork (fun () -> f (id * 2 + 1) (depth - 1));
    log "Forking number %i\n%!" (id * 2 + 2);
    fork (fun () -> f (id * 2 + 2) (depth - 1))
  end else begin
    log "Yielding in number %i\n%!" id;
    yield ();
    log "Resumed number %i\n%!" id;
  end;
  log "Finishing number %i\n%!" id

let () = run (fun () -> f 0 2)