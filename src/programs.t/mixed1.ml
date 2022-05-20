
effect Foo : int -> (unit -> unit)

let f n = 
  (* Foo(n).Foo(n)? *)
  print_string ("once " ^ string_of_int n ^ "\n");
  let a = perform (Foo n) in 
  a () 

let rec send n = 
  match f n with 
  (* Foo(n).Foo(n)?() *)
  (* n>=0 /\ Foo^* \/ n<0 /\ Foo^w *)
  | _ -> ()
  | effect (Foo 0) k -> ()
  | effect (Foo v) k -> send (n-1)

(*
     n=0/\emp \/ n>0 /\ Foo(n).Foo^* \/ n <0/\ Foo.Foo^w

     *)
    
let main = send 5 
