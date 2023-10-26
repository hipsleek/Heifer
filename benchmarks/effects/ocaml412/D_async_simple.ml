(* An algebraically well-behaved implementation of async/await with
   multi-shot continuations.

https://github.com/ocaml-multicore/effects-examples/blob/master/sched.ml
*)


effect Fork : (unit -> unit) -> unit
effect Yield : unit

let fork f = perform (Fork f)
let yield () = perform Yield

let queue_create () = ref ([], [])

let queue_push ele queue =
  let (front, back) = !queue in
  queue := (front, ele::back)

let queue_is_empty queue =
  let (front, back) = !queue in
  List.length front = 0 && List.length back = 0

let _queue_length queue =
  let (front, back) = !queue in
  List.length front + List.length back

let rev_list l =
  let rec rev_acc acc = function
    | [] -> acc
    | hd::tl -> rev_acc (hd::acc) tl
  in
  rev_acc [] l

let queue_pop queue =
  let (front, back) = !queue in
  match front with
  | h::tl ->
    queue := (tl, back);
    h
  | [] ->
    (match rev_list back with
    | [] -> raise (Failure "dequeue-ing an empty queue")
    | h::newfront ->
        queue := (newfront, []);
        h)

(* A concurrent round-robin scheduler *)
let run main
(*@ run(main, ()): req ture; ex queue; (isEmpty(queue), Norm(())) @*)
=
  let run_q = queue_create () in
  let enqueue k = queue_push k run_q in
  let dequeue ()
  (*@ req NoEff(hd, tl(run_q), n); ens(run_q', n') /\ n'<n @*)
  = if queue_is_empty run_q then
      (print_endline ("empty equeue");
      () )
    else continue (queue_pop run_q) ()
  in

  let rec spawn f =
    (*@ req NoEff(f, queue, 0); (true, Norm()) @*)
    (*@ req NoEff(f, queue, n); (NoEff(f', queue', n') /\ n'<n,  Norm()) @*)

    (* the total effects in f and queue is decreasing...
       NoEff(f, queue, 0), here the f become the hd of the queue from time to time.
    *)

    match f () with
    (*@ match_with (f, queue, res):
        req NoEff(f, queue, 0); (true, Norm())
        req NoEff(f, queue, n); (NoEff(f', queue', n') /\ n'<n,  Norm())
    @*)
    | () ->
          (*print_endline ("queue length " ^ string_of_int (_queue_length run_q));*)
          if queue_is_empty run_q then ()
          else continue (queue_pop run_q) ()
    | exception e ->
            print_string (Printexc.to_string e);
            dequeue ();
    | effect Yield k ->
       enqueue k;
       dequeue ()
    | effect (Fork f') k ->
       enqueue k;
       spawn f'
  in
  spawn main;
  assert (queue_is_empty run_q)

let task name () =
  Printf.printf "starting %s\n%!" name;
  Printf.printf "yielding %s\n%!" name;
  yield ();
  Printf.printf "ending %s\n%!" name;
  ()

let main () =
  (*let pa = fork (task "a") in
  let _pb = fork (task "b") in
  let _pc = fork (task "c") in
  let _pe = fork (task "b") in
  let _pd = fork (task "c") in
  *)

  let p_total = (fork (fun () -> fork (task "a"); fork (task "b") )) in
  p_total

let _ = run main
