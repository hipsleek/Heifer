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

(* predicate queue_push(ele, queue) 
= ex mm mm' w inter; req any_queue(queue, mm) /\ effNo(ele)=w; 
  Norm(non_empty_queue(queue, mm') /\ mm'=mm+w /\ res=inter /\ inter=()) @*)

(* predicate queue_is_empty(queue) 
=  ex inter; req empty_queue(queue); Norm(empty_queue(queue) /\ res=inter /\ inter=true)
\/ ex m inter; req non_empty_queue(queue, m);  Norm(non_empty_queue(queue, m) /\ res=inter /\ inter=false) @*)


(* predicate queue_pop (queue) 
= ex m m' w f; req non_empty_queue(queue, m);  
  Norm(any_queue(queue, m') /\ effNo(f) =w /\ m'+w=m /\ res=f) @*)

let queue_create () = ref ([], [])

let queue_push ele queue 
(*@ ex mm mm' w inter; req any_queue(queue, mm); 
  Norm(non_empty_queue(queue, mm') /\ effNo(ele)=w /\ w >0 /\ mm'=mm+w /\ res=inter /\ inter=()) @*)
= let (front, back) = !queue in
  queue := (front, ele::back)

let queue_is_empty queue 
(*@ ex inter; req empty_queue(queue); Norm(empty_queue(queue) /\ res=inter /\ inter=true)
\/ ex m inter; req non_empty_queue(queue, m);  Norm(non_empty_queue(queue, m) /\ res=inter /\ inter=false) @*)
= let (front, back) = !queue in
  List.length front = 0 && List.length back = 0

let rev_list l =
  let rec rev_acc acc = function
    | [] -> acc
    | hd::tl -> rev_acc (hd::acc) tl
  in
  rev_acc [] l

let queue_pop queue 
(*@ ex m m' w f; req non_empty_queue(queue, m);  
  Norm(any_queue(queue, m') /\ effNo(f) =w /\ w >0 /\ m'+w=m /\ res=f) @*)
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


let enqueue f run_q
(*@ ex r; queue_push(f, run_q, r); Norm(res=r) @*)
= queue_push f run_q

let wrapPop run_q 
(*@ ex f; queue_pop (run_q, f); Norm (res=f)@*)
=  queue_pop run_q

let dequeue run_q
(*@ queue_is_empty(run_q, true); Norm(res=())
\/  ex m m' w f cr; req non_empty_queue(run_q, m);  
    Norm(any_queue(run_q, m') /\ effNo(f) =w /\ w >0 /\ m'+w=m );
    continue (f, (), cr); Norm(res=cr)
@*)
= if queue_is_empty run_q then ()
  else 
    let f = queue_pop run_q in 
    continue f ()


(*@ predicate f(arg) = 
      ex r r1 r2; Yield(emp, r1); f2(r2);
      Norm(effNo(f)=n /\ n>0 /\ effNo(f2)=n-1 /\ res = r /\ r= ()) 
@*)



let rec spawn f run_q 
(*@ ex m m' w w' ele cr; req any_queue(run_q, m);  
   Norm(any_queue(run_q, m') /\ effNo(f)=w /\ effNo(ele) =w' /\ w>0 /\ w'>0 /\ (w'+m')<(m+w) );
   spawn (ele, run_q, cr); Norm(res=cr)
@*)
= match f () with
  (*@ spawn (f, run_q, res) @*)
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


req run_q->v1201/\effNo(v1201)=v1197/\v1197>=0; 
Norm(run_q->v1202/\effNo(v1202)=v1198/\v1198>0/\effNo(f2)=v1199/\v1199>0/\v1198=v1197+v1199/\v1195=()/\v1221=v1195); 
Norm(emp); ex v1205 v1206 v1207 v1208; 
req run_q->v1207/\effNo(v1207)=0; 
Norm(run_q->v1208/\effNo(v1208)=0/\v1205=true/\res=()) 


req run_q->v1201/\effNo(v1201)=v1197/\v1197>=0/\effNo(v1207)=0/\v1202=v1207; 
Norm(run_q->v1208/\effNo(v1202)=v1198/\v1198>0/\effNo(f2)=v1199/\v1199>0/\v1198=v1197+v1199/\v1221=()/\v1207=v1202/\effNo(v1208)=0/\v1205=true/\res=())
*)

