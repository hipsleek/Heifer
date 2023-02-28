
(* https://patrick.sirref.org/posts/escaping-effects *)

effect A : (unit -> unit) -> unit
effect B : string

let do_a f = perform (A f)
let run_a f =
  match f () with
  | effect (A f) k ->
    print_endline ("handling A");
    f ();
    continue k ()
  | v -> v

let do_b () = perform B
let run_b f =
  match f () with
  | effect B k ->
    print_endline ("handling B");
    continue k "B"
  | v -> v

let unhandled () =
  run_a @@ fun _ ->
    run_b @@ fun _ ->
      do_a (fun () ->
        print_endline (do_b ()))

let ok () =
  run_b @@ fun _ -> (* only change how handlers are nested *)
    run_a @@ fun _ ->
      do_a (fun () ->
        print_endline (do_b ()))

let () =
  ok ();
  print_endline "---";
  unhandled ()