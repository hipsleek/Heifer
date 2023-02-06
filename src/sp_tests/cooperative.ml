effect Async : (unit -> unit) -> unit 
effect Yield : unit 

let i = Sys.opaque_identity (ref 0)

let async f 
(*@  requires (true, _^* ) @*)
(*@ ensures (true, Async (f)) @*)
= perform (Async f)

let yield ()
(*@  requires (true, _^* ) @*)
(*@ ensures (true, Yield) @*)
= perform Yield

let q = Queue.create ()
let enqueue t = Queue.push t q
let dequeue () =
    if Queue.is_empty q then ()
    else Queue.pop q ()

let rec handler prog =
  match prog () with 
  | v -> dequeue () 
  | effect (Async f) k -> 
    enqueue (continue k); 
    handler f
  | effect Yield k -> 
    enqueue (continue k);
    dequeue ()

let task1 () 
(*@  requires (true, _^* ) @*)
(*@  ensures  (true, {i->i+3}.Yield.{i->i+6}.Yield) @*)
= 
  Printf.printf "adding %s\n%!" (string_of_int 3);
  i := !i + 3;
  Printf.printf "current i = %s\n%!" (string_of_int !i);
  yield (); 
  Printf.printf "adding %s\n%!" (string_of_int 6);
  i := !i + 6;
  Printf.printf "current i = %s\n%!" (string_of_int !i);
  yield ()

let task2 () 
(*@  requires (true, _^* ) @*)
(*@  ensures  (true, {i->i+7}.Yield) @*)
= 
  Printf.printf "adding %s\n%!" (string_of_int 7);
  i := !i + 7;
  Printf.printf "current i = %s\n%!" (string_of_int !i);
  yield ()

let main () =
  async (task1);
  async (task2)

let _ = handler main 

