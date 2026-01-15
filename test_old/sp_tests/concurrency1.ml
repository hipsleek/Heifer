open Thread

effect Write : int -> unit 

let n = int_of_float (Sys.time() *. 1000000.0) 

let () = Random.init (n)

let (i: int ref) = Sys.opaque_identity (ref 0)

let write i = 
  print_string ("adding " ^ string_of_int i ^"\n");
  Write i

let prog () = 
  let _ = (Thread.create write 1) in 
  let _ = (Thread.create write 2) in 
  (Thread.create write 3) 


let main 
  (*@ requires _^* @*)
  (*@ ensures {v->1} || {v->2} || {v->3}  @*)
= 
  match (Thread.join (prog ())) with 
  | x -> x
  | effect (Write x) k -> 
    let fn = (Random.float 1.0) in 
    Thread.delay fn;
    i := !i + x;
    print_endline ("Value " ^ string_of_int !i);
    (continue k ())


