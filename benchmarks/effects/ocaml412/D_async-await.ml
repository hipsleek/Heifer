(* An algebraically well-behaved implementation of async/await with
   multi-shot continuations.

https://github.com/ocaml-multicore/effects-examples/blob/master/sched.ml
*)

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

  effect Await : 'a Promise.t -> 'a
  effect Fork : bool
  effect Yield : unit


  exception End_of_strand

  let await : 'a Promise.t -> 'a
    = fun pr -> perform (Await pr)

  let fork : unit -> bool
    = fun () -> perform Fork

  let yield : unit -> unit
    = fun () -> perform Yield

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

    (* let hsched : unit -> (unit, unit) Effect.Deep.handler *)
      (* = fun () -> *)
    let run : (unit -> unit) -> unit
    = fun f ->
      let state = { suspended = Queue.create () } in
      match f () with
      | () -> run_next state
      | exception End_of_strand -> run_next state
      | exception e -> raise e
      | effect (Await pr) k ->
         (if Promise.is_done pr
          then continue k (Promise.value pr)
          else Promise.wait pr (fun v -> continue k v));
         run_next state

      | effect Fork k ->
         enqueue state (fun () -> continue k false);
         continue (Obj.clone_continuation k) true

      | effect Yield k ->
         enqueue state (fun () -> continue k ());
         run_next state
  end

  let run = Scheduler.run

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
  let task1 name () = Async.yield (); 1 in 
  let (pa:int Async.Promise.t) = Async.async (task1 "a") in
  let (pb:unit Async.Promise.t) = Async.async (task "b") in
  let (pc:unit Async.Promise.t) = Async.async (task "c") in
  let (pc:unit Async.Promise.t) = Async.async (fun () -> print_endline (string_of_int (Async.await pa)); Async.await pb)
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
