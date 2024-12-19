effect Open : int -> unit
effect Close: int -> unit

let open_file n
(*@ requires (true, (_ ^* ) , ())  @*)
(*@ ensures (true, Open(n)!, ()) @*)
= perform (Open n)

let close_file n
(*@ requires (true, (_ ^* ) .(Open(n)!).((~ Close(n)!)^* ) , ())  @*)
(*@ ensures (true, Close(n)!, ()) @*)
= perform (Close n)

let file_9 () 
(*@ requires (true, emp, ()) @*)
(*@ ensures (true, (Open(9)!).(Open(8)!).(Close(9)!).(Close(8)!), ()) @*)
= 
  open_file 9;
  open_file 8;
  close_file 9


let main 
(*@ requires (true, emp, ()) @*)
(*@ ensures (true, Open(9). ((~Close(9))^* ) .Close(9) \/ (Open(8). ((~Close(8))^* ) .Close(8)), ()) @*)
= 
  match file_9 () with 
  | _ -> ()
  | effect (Open n) k -> continue k ()
  | effect (Close n) k -> continue k ()
