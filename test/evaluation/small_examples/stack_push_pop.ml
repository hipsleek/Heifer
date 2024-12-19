effect Push : 'a -> unit
effect Pop : unit -> 'a option

let push_stack value 
=
  perform (Push value)

let pop_stack () 
=
  perform (Pop ())

let test ()
= 
  push_stack 1;
  pop_stack ();
  match pop_stack () with
    | Some top -> top
    | none -> none
  
let stack_handler () 
=
  let stack = ref [] in
  match test () with
  | v -> v
  | effect (Push value) k -> stack := value :: !stack; (continue k stack);
  | effect (Pop ()) k ->
    match !stack with
    | [] -> (continue k []);
    | top :: rest -> stack := rest; (continue k (Some top));
