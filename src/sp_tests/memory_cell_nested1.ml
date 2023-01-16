effect Read : int 
effect Write : int -> unit 

let (i: int ref) = Sys.opaque_identity (ref 0)

let read () 
(*@ requires _^*  @*)
(*@ ensures Read @*)
= perform Read

let write n 
(*@ requires _^*  @*)
(*@ ensures (Write n) @*)
= perform (Write n)

let client () 
(*@ requires _^*  @*)
(*@ ensures Read. (write 10). Read @*)
= let x = read () in 
  Printf.printf "i = %d\n%!" x;
  write 10;
  let x = read () in 
  Printf.printf "i = %d\n%!" x

let handler1 () 
(*@ requires {i->0}  @*)
(*@ ensures (write 10) ??? the stack value is untracked @*)
= 
  match client () with
  | v -> ()
  | effect Read k -> (continue k (!i))


let main 
(*@ requires emp  @*)
(*@ ensures emp @*)
=
  match handler1 () with
  | v -> ()
  | effect (Write x) k -> i := x; (continue k ())


(*      
For main:  
{i->0}. Read. (write 10). Read
    currenct effects       continuation k                statck     /\ heap     /\ assertion 
    --------------------------------------------------------------------------------
    {i->0}                 Read. (write 10). Read                      i=0
    Read                   (write 10). Read               0         /\ i=0
    (write 10)             {i->x}. Read                   0; x=10   /\ i=0
    {i->x}                 Read                           0; x=10   /\ i=10
    Read                   emp                            10;x=10   /\ i=10
*)