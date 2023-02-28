effect Async : (unit -> unit) -> unit 
effect Yield : unit 

let i = Sys.opaque_identity (ref 0)

let async f 
(*@  requires (true, emp ,()) @*)
(*@ ensures (true, Async (f),()) @*)
= perform (Async f)

let yield ()
(*@  requires (true,emp ,()) @*)
(*@ ensures (true, Yield,()) @*)
= perform Yield

let q = Queue.create ()
let enqueue t = Queue.push t q
let dequeue () =
    if Queue.is_empty q then ()
    else Queue.pop q ()

let task1 () 
(*@  requires (true, emp ,()) @*)
(*@  ensures  (true, {i->i+3}.Yield.{i->i+6},()) @*)
= 
  Printf.printf "adding %s\n%!" (string_of_int 3);
  i := !i + 3;
  Printf.printf "current i = %s\n%!" (string_of_int !i);
  yield (); 
  Printf.printf "adding %s\n%!" (string_of_int 6);
  i := !i + 6;
  Printf.printf "current i = %s\n%!" (string_of_int !i)
  

let task2 () 
(*@  requires (true, emp ,()) @*)
(*@  ensures  (true, {i->i+7},()) @*)
= 
  Printf.printf "adding %s\n%!" (string_of_int 7);
  i := !i + 7;
  Printf.printf "current i = %s\n%!" (string_of_int !i)


let task3 () 
(*@  requires (true, emp ,()) @*)
(*@  ensures  (true, [i=16].{i->i+9},()) @*)
=
  Printf.printf "adding %s\n%!" (string_of_int 9);
  assert (!i = 16);
  i := !i + 9;
  Printf.printf "current i = %s\n%!" (string_of_int !i)


let prog () 
(*@ requires (true, emp ,()) @*)
(*@ ensures (true, Async(task1).Async(task2).Async(task3),()) @*)
=
  async (task1);
  async (task2);
  async (task3)

let rec handler arg_f =
  match arg_f () with 
  | v -> dequeue () 
  | effect (Async f1) k -> 
    enqueue (continue k)
    ; handler f1  
  | effect Yield k -> 
    enqueue (continue k);
    dequeue ()

let main 
(*@ requires (true, emp ,()) @*)
(*@ ensures (true, {i->i+3}.{i->i+7}.{i->i+6}.[i=16].{i->i+9},()) @*)
= handler prog 


(*
Async(() -> {i->i+3}.Yield.{i->i+6}).
Async(() -> {i->i+7}).
Async(() -> {i->i+9})

{q->q.enqueue(Async(task2).Async(task3))}.{i->i+3}.{q->q.enqueue({i->i+6})}.{q->q.enqueue{task3}}.{i->i+7}.{i->i+6}.{i->i+9}


{i->i+3}.{enqueue({i->i+6})}.
{enqueue(Async(() -> {i->i+9}))}.{i->i+7}.{i->i+6}.{i->i+9}

q:
Async(() -> Yield.{i->i+7}.Yield)
Async(() -> {i->i+9}.Yield)
--------------------------
{i->i+3}.Yield.{i->i+6}.Yield
---------------------------

*)