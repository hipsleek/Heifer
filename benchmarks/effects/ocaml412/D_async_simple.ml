(* An algebraically well-behaved implementation of async/await with
   multi-shot continuations.

https://github.com/ocaml-multicore/effects-examples/blob/master/sched.ml *)


effect Fork : (unit -> unit) -> unit
effect Yield : unit

let fork f 
(*@ ex r; Fork(emp, f, r); Norm(res=r) @*)
= perform (Fork f)
let yield () 
(*@ ex r; Yield(emp, r); Norm(res=r) @*)
= perform Yield 


(*@ ~predicate any_queue(queue, m) 
= ex q; queue->q /\ effNo(q) = m /\ m>=0 @*)

(*@ ~predicate non_empty_queue(queue, m) 
= ex q; queue->q /\ effNo(q) = m /\ m>0 @*)

(*@ ~predicate empty_queue(queue) 
= ex q; queue->q /\ effNo(q) = 0   @*)

(*@ predicate queue_push(ele, queue, res) 
= ex m m' w; req any_queue(queue, m) /\ effNo(ele)=w; 
  Norm(non_empty_queue(queue, m') /\ m'=m+w /\ res=()) @*)

(*@ predicate queue_is_empty(queue, res) 
=  req empty_queue(queue); Norm(empty_queue(queue) /\ res=true)
\/ ex m; req non_empty_queue(queue, m);  Norm(non_empty_queue(queue, m) /\ res=false) @*)


(*@ predicate queue_pop (queue, f') 
= ex m m'; req non_empty_queue(queue, m);  
  Norm(any_queue(queue, m') /\ effNo(f') =w /\ m'+w=m /\ res=f') @*)


(*
let queue_create () = ref ([], [])

let queue_push ele queue 
= let (front, back) = !queue in
  queue := (front, ele::back)

let queue_is_empty queue =
  let (front, back) = !queue in
  List.length front = 0 && List.length back = 0

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
*)

let enqueue ele queue
(*@ ex r; queue_push(ele, queue, r) @*)
= queue_push ele queue

let dequeue queue
(*@ queue_is_empty(queue, true); Norm(res=())
\/  queue_is_empty(queue, false);
    queue_pop (queue, f1);
    continue (f2, ())
@*)
= if queue_is_empty queue then ()
  else continue (queue_pop queue) ()

(*


(*@ f(r) = 
       ens effNo(f) = 0 /\ r = () /\ res=r
    \/ ex r1 r2 r3; Fork(f1, r2); f2(r3); 
       ens effNo(f)=n /\ n>0 /\ effNo(f1)+effNo(f2)=n-1 /\ res = ()  
    \/ ex r1 r2; Yield(r1); f1(r2); 
       ens effNo(f)=n /\ n>0 /\ effNo(f1)=n-1 /\ res = ()   @*)


(*@ predicate 
spawn (f, queue, f', res) = 
  req empty_queue(queue) /\ effNo(f)=0; ens res = () 
  \/
  ex m w; req any_queue(queue, m) /\ effNo(f)=w; 
  Norm (any_queue(queue, m') /\ effNo(f')=w' /\ m'+w' < m+w  /\ res=())
@*)

(*@ predicate 
match (f, queue, f', res) = spawn (f, queue, f', res)
@*)

(* A concurrent round-robin scheduler *)
let run main
= let run_q = queue_create () in
  let rec spawn f = 
    match f () with
    | () ->
       dequeue run_q;
    | effect Yield k ->
       enqueue k run_q;
       dequeue run_q
    | effect (Fork f') k ->
       enqueue k run_q;
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

  let p_total = (yield ();fork (fun () -> fork (task "a"); fork (task "b") )) in
  p_total

let _ = run main



*)