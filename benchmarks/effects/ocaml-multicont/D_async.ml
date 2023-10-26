(* An algebraically well-behaved implementation of async/await with
   multi-shot continuations. 
   
https://github.com/ocaml-multicore/effects-examples/blob/master/sched.ml   
*)
open Multicont.Deep

module Async: sig
  module Promise: sig
    type 'a t
  end

  val await : 'a Promise.t -> 'a
  val async : (unit -> 'a) -> 'a Promise.t
  val yield : unit -> unit
  val run : (unit -> unit) -> unit
end = struct

  module Promise = struct
    type 'a promise = Done of 'a
                    | Pending of ('a -> unit) list
    type 'a t = 'a promise ref

    let is_done : 'a t -> bool
      = fun pr -> match !pr with
                  | Done _ -> true
                  | _ -> false

    let wait : 'a t -> ('a -> unit) -> unit
      = fun pr r -> match !pr with
                    | Done _ -> assert false
                    | Pending rs -> pr := Pending (r :: rs)

    let value : 'a t -> 'a
      = fun pr -> match !pr with
                  | Done v -> v
                  | Pending _ -> assert false

    let make_empty : unit -> 'a t
      = fun () -> ref (Pending [])
  end

  type _ Effect.t += Await : 'a Promise.t -> 'a Effect.t
                   | Fork : bool Effect.t
                   | Yield : unit Effect.t


  exception End_of_strand

  let await : 'a Promise.t -> 'a
    = fun pr -> Effect.perform (Await pr)

  let fork : unit -> bool
    = fun () -> Effect.perform Fork

  let yield : unit -> unit
    = fun () -> Effect.perform Yield

  let async : (unit -> 'a) -> 'a Promise.t
    = fun f ->
    let pr = Promise.make_empty () in
    if fork () (* returns twice *)
    then pr
    else let v = f () in
         (match !pr with
          | Done _ -> assert false
          | Pending rs ->
             pr := Done v;
             List.iter (fun r -> r v) rs);
         raise End_of_strand

  module Scheduler = struct

    type state = { suspended: (unit -> unit) Queue.t }

    let enqueue :  state -> (unit -> unit) -> unit
      = fun st r ->
      Queue.add r st.suspended

    let run_next : state -> unit
      = fun st ->
      if Queue.is_empty st.suspended then ()
      else Queue.take st.suspended ()

    let hsched : unit -> (unit, unit) Effect.Deep.handler
      = fun () ->
      let state = { suspended = Queue.create () } in
      let open Effect.Deep in
      { retc = (fun () -> run_next state)
      ; exnc = (fun e ->
        match e with
        | End_of_strand -> run_next state
        | e -> raise e)
      ; effc = (fun (type a) (eff : a Effect.t) ->
        match eff with
        | Await pr -> Some (fun (k : (a, unit) continuation) ->
          (if Promise.is_done pr
           then continue k (Promise.value pr)
           else Promise.wait pr (fun v -> continue k v));
           run_next state)

        | Fork -> Some (fun (k : (bool, unit) continuation) ->
          let r = promote k in
          enqueue state (fun () -> resume r false);
          resume r true)
          
        | Yield -> Some (fun (k : (unit, unit) continuation) ->
          enqueue state (fun () -> continue k ());
          run_next state)
        | _ -> None) }
  end

  let run : (unit -> unit) -> unit
  = fun f -> Effect.Deep.match_with f () (Scheduler.hsched ())
end

(* The `well-behaveness' of this implementation can be illustrated by
   using it in conjunction with another effect. In each async strand
   any occurrence of `Ask' is correctly bound by an ambient
   `Env.bind'. *)
let main () =
  let task name () =
    Printf.printf "starting %s\n%!" name;
    Printf.printf "yielding %s\n%!" name;
    Async.yield ();
    Printf.printf "ending %s\n%!" name;
    ()
  in
  let pa = Async.async (task "a") in
  let pb = Async.async (task "b") in
  let pc = Async.async (fun () -> Async.await pa; Async.await pb)
  in
  (*Printf.printf "Sum is %d\n" (Async.await pc);
  assert Async.(await pa + await pb = await pc)*)
  (Async.await pc);
  ()

let _ = Async.run main

(* The following program would deadlock if cyclic
   promise resolution was allowed *)
(*let try_deadlock () =
   let pr = ref (fun () -> assert false) in
   let task () =
     Async.await (!pr ())
   in
   print_endline "Fork task";
   let pr' = Async.async task in
   pr := (fun () -> pr');
   print_endline "Await";
   Async.await (!pr ())

let _ = Async.run try_deadlock 
*)
