
(* https://patrick.sirref.org/posts/escaping-effects *)

(* Cooperative concurrency.
   Takes a function to run at some later point. *)
effect Async : (unit -> unit) -> unit

(* Reader monad/environment effect.
   Allows reading global values *)
effect Env : string

let async f = perform (Async f)
let run_a f =
  match f () with
  | effect (Async f) k ->
    print_endline ("handling Async");
    f ();
    continue k ()
  | v -> v

let read () = perform Env
let run_b f =
  match f () with
  | effect Env k ->
    print_endline ("handling Env");
    continue k "Env"
  | v -> v

let unhandled () =
  run_a (fun () ->
    run_b (fun () ->
      async (fun () ->
        print_endline (read ()))))

let ok () =
  run_b (fun () -> (* only change how handlers are nested *)
    run_a (fun () ->
      async (fun () ->
        print_endline (read ()))))

let () =
  ok ();
  print_endline "---";
  unhandled ()
