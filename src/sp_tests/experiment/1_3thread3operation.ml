effect Async : (unit -> unit) -> unit 
effect Yield : unit 

let i = Sys.opaque_identity (ref 0)

let async f 
(*@  requires (true, emp ,()) @*)
(*@ ensures (true, Async (f),()) @*)
= perform (Async f)

let yield ()
(*@  requires (true, emp ,()) @*)
(*@ ensures (true, Yield,()) @*)
= perform Yield

let q = Queue.create ()
let enqueue t = Queue.push t q
let dequeue () =
    if Queue.is_empty q then ()
    else Queue.pop q ()

let task1 () 
(*@  requires (true, emp ,()) @*)
(*@  ensures  (true, {i->i+3}.Yield.{i->i+6}.Yield.{i->i+10},()) @*)
= 
  Printf.printf "adding %s\n%!" (string_of_int 3);
  i := !i + 3;
  yield (); 
  Printf.printf "adding %s\n%!" (string_of_int 6);
  i := !i + 6;
  yield (); 
  Printf.printf "adding %s\n%!" (string_of_int 10);
  i := !i + 10
  

let task2 () 
(*@  requires (true, emp ,()) @*)
(*@  ensures  (true, {i->i+7}.Yield.{i->i+61}.Yield.{i->i+110},()) @*)
= 
  Printf.printf "adding %s\n%!" (string_of_int 7);
  i := !i + 7;
  yield (); 
  Printf.printf "adding %s\n%!" (string_of_int 61);
  i := !i + 61;
  yield (); 
  Printf.printf "adding %s\n%!" (string_of_int 110);
  i := !i + 110



let task3 () 
(*@  requires (true, emp ,()) @*)
(*@  ensures  (true, {i->i+9}.Yield.{i->i+16}.Yield.{i->i+101},()) @*)
=
  Printf.printf "adding %s\n%!" (string_of_int 9);
  i := !i + 9;
  yield (); 
  Printf.printf "adding %s\n%!" (string_of_int 16);
  i := !i + 16;
  yield (); 
  Printf.printf "adding %s\n%!" (string_of_int 101);
  i := !i + 101


let prog () 
(*@ requires (true, emp ,()) @*)
(*@ ensures (true, Async(task3).Async(task2).Async(task1),()) @*)
=
  async (task3);
  async (task2);
  async (task1)

let rec handler arg_f =
  match arg_f () with 
  | v -> dequeue () 
  | effect (Async f) k -> 
    enqueue (continue k)
    ; handler f  
  | effect Yield k -> 
    enqueue (continue k);
    dequeue ()

let main 
(*@ requires (true, emp ,()) @*)
(*@ ensures (true, {i->0}.{i->i+9}.{i->i+7}.{i->i+16}.{i->i+3}.
{i->i+61}.{i->i+101}.{i->i+6}.{i->i+110}.{i->i+10},323) @*)
= 
let i = Sys.opaque_identity (ref 0) in 
handler prog ;
print_string (string_of_int !i)

