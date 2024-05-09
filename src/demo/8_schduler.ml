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

(* seperation logic predicates are starting with a ~ *)
(*@ ~predicate any_queue(queue, m) 
= ex q; queue->q /\ effNo(q) = m /\ m>=0 @*)

(*@ ~predicate non_empty_queue(queue, m) 
= ex q; queue->q /\ effNo(q) = m /\ m>0 @*)

(*@ ~predicate empty_queue(queue) 
= ex q; queue->q /\ effNo(q) = 0   @*)

let queue_create () = ref ([], [])

let queue_push ele queue 
(*@
ex m m' q q'; req queue->q /\ effNo(q) = m /\ m>=0; 
ens  queue->q' /\ effNo(q') = m' /\ m'>0 /\ effNo(ele)=w /\ w >0 /\ m'=m+w /\ res=() 
@*)
= let (front, back) = !queue in
  queue := (front, ele::back)



(* ex inter; req empty_queue(queue); Norm(empty_queue(queue) /\ res=true /\ inter=true)
\/ ex m inter; req non_empty_queue(queue, m);  Norm(non_empty_queue(queue, m) /\ res=false) *)
let queue_is_empty queue 
(*@ ex q ; req queue->q /\ effNo(q)=0; ens queue->q /\ res=true 
\/  ex q ; req queue->q /\ effNo(q)>0; ens queue->q /\ res=false @*)
= let (front, back) = !queue in
  List.length front = 0 && List.length back = 0

let rev_list l =
  let rec rev_acc acc = function
    | [] -> acc
    | hd::tl -> rev_acc (hd::acc) tl
  in
  rev_acc [] l

(* ex m m' w f; req non_empty_queue(queue, m);  
  Norm(any_queue(queue, m') /\ effNo(f) =w /\ w >0 /\ m'+w=m /\ res=f) *)
let queue_pop queue 
(*@
ex m m' q q' f w; 
req queue->q /\ effNo(q) = m /\ m>0; 
ens  queue->q' /\ effNo(q') = m' /\ m'>=0  /\ effNo(f) =w /\ w >0 /\ m'+w=m /\  res = f 
@*)
= let (front, back) = !queue in
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

(* ex f; queue_pop (run_q, f); Norm (res=f)*)
let wrapPop run_q 
(*@
ex m m' q q' f w; 
req run_q->q /\ effNo(q) = m /\ m>0; 
ens  run_q->q' /\ effNo(q') = m' /\ m'>=0  /\ effNo(f) =w /\ w >0 /\ m'+w=m /\  res = f 
@*)
=  queue_pop run_q

(* ex mm mm' w inter; req any_queue(queue, mm); 
  Norm(non_empty_queue(queue, mm') /\ effNo(ele)=w /\ w >0 /\ mm'=mm+w /\ res=inter /\ inter=()) *)
let enqueue ele queue
(*@
ex m m' q q'; req queue->q /\ effNo(q) = m /\ m>=0; 
ens  queue->q' /\ effNo(q') = m' /\ m'>0 /\ effNo(ele)=w /\ w >0 /\ m'=m+w /\ res=() 
@*)
= queue_push ele queue

(* queue_is_empty(run_q, true); Norm(res=())
\/  queue_is_empty(run_q, false); 
    ex m m' w f cr; req non_empty_queue(run_q, m);  
    Norm(any_queue(run_q, m') /\ effNo(f) =w /\ w >0 /\ m'+w=m );
    continue (f, (), cr); Norm(res=cr) *)
let dequeue run_q
(*@
ex q; req run_q->q /\ effNo(q)=0; ens run_q->q  /\ res=()   
\/ 
ex m m' q q' f w;  
req run_q->q /\ effNo(q)=m /\ m >0; 
ens run_q->q' /\ effNo(q') = m' /\ m'>=0  /\ effNo(f)=w /\ w >0 /\ m'+w=m;
ex cr; continue_syh (f, (), cr)
@*)
= if queue_is_empty run_q then ()
  else 
    let f = queue_pop run_q in 
    continue_syh f ()

(*@ predicate task(f) = 
     Norm(effNo(f) = 0 /\ res=())
   \/ex n r1 f2; ens effNo(f)=n/\n>0/\effNo(f2)=n-1; Yield(emp, r1); task(f2)
   \/ex r r1 f1 f2 r2 n m1 m2; 
     ens effNo(f)=n /\ n>0 /\ effNo(f1)= m1 /\ effNo(f2)=m2 /\ m1>0 /\ m2>0 /\ (m1+m2)=(n-1); 
     Fork(emp, f1, r1); task(f2) 
@*)
    

let rec spawn f run_q 
(*@ ex r; queue_is_empty(run_q, true) ; ens effNo(f)=0 /\ res =r /\ r= () 
\/ ex m m' w w' ele cr; req non_empty_queue(run_q, m);  
   Norm(any_queue(run_q, m') /\ effNo(f)=0 /\ effNo(ele) =w' /\ m'<m );
   spawn (ele, run_q, cr); Norm(res=cr)
\/ ex m m' w w' ele cr qq mm; req any_queue(run_q, m) /\ effNo(qq)=mm /\ mm>0 ;  
    Norm(any_queue(run_q, m') /\ effNo(f)=w /\ effNo(ele) =w' /\ w>0 /\ w'>0 /\ (w'+m')<(m+w) );
    spawn (ele, run_q, cr); Norm(res=cr)
@*)
= match f () with
  (* spawn (f, run_q, res) *)
  | x -> dequeue run_q;
  | effect Yield k ->
     enqueue k run_q;
     dequeue run_q
  | effect (Fork f') k -> 
     enqueue k run_q; 
     spawn f' run_q


(*
(* A concurrent round-robin scheduler *)
let run main
(*@ ex queue q r; Norm (queue->q /\ effNo(q)=0 /\ res = r /\ r = ()) @*)
= let run_q = queue_create () 
  in spawn main run_q

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