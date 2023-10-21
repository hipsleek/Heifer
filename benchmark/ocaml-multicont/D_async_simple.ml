(* An algebraically well-behaved implementation of async/await with
   multi-shot continuations. 
   
https://github.com/ocaml-multicore/effects-examples/blob/master/sched.ml   
*)

open Effect
open Effect.Deep

type _ Effect.t += Fork : (unit -> unit) -> unit Effect.t
type _ Effect.t += Yield : unit Effect.t

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
    match_with f ()
      {
        retc = (fun () -> dequeue ());
        exnc =
          (fun e ->
            print_string (Printexc.to_string e);
            dequeue ());
        effc =
          (fun (type a) (e : a Effect.t) ->
            match e with
            | Yield ->
                Some
                  (fun (k : (a, unit) continuation) ->
                    enqueue k;
                    dequeue ())
            | Fork f ->
                Some
                  (fun (k : (a, unit) continuation) ->
                    enqueue k;
                    spawn f)
            | _ -> None);
      }
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
  let pb = fork (task "b") in
  let pc = fork (fun () -> pa; pb)
  in
  (*Printf.printf "Sum is %d\n" (await pc);
  assert (await pa + await pb = await pc)*)
  (pc);
  ()

let _ = run main

(* The following program would deadlock if cyclic
   promise resolution was allowed *)
(*let try_deadlock () =
   let pr = ref (fun () -> assert false) in
   let task () =
     await (!pr ())
   in
   print_endline "Fork task";
   let pr' = async task in
   pr := (fun () -> pr');
   print_endline "Await";
   await (!pr ())

let _ = run try_deadlock 
*)
