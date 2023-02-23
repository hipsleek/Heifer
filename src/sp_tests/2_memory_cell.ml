effect Read :  (int ref )-> int 
effect Write : (int ref * int) -> unit 

let read x 
(*@  requires (true, _^* , ()) @*)
(*@  ensures  (true, Read (x), ()) @*)
= perform (Read x)

let write i n 
(*@  requires (true, _^* , ()) @*)
(*@ ensures (true, Write (i n), ()) @*)
= perform (Write (i, n))

let client i 
(*@ requires (true, _^* , ()) @*)
(*@ ensures (true, Read(i). (Write (i 10)). Read(i), ()) @*)
= let x = read i in 
  Printf.printf "i = %d\n%!" x;
  write i 10;
  let x = read i in 
  Printf.printf "i = %d\n%!" x

let main 
(*@  requires (true, emp , ()) @*)
(*@ ensures  (true, {i->0}.{i->10}, () )  @*)
=
  let i = Sys.opaque_identity (ref 0) in
  match client i with
  | v -> ()
  | effect (Read x) k -> (continue k (!x))
  | effect (Write (x, n)) k -> x := n; (continue k ())

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