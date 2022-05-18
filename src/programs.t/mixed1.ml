
effect Foo : int -> (unit -> unit)

let f n = 
  (* Foo(n).Foo(n)? *)
  print_string ("once " ^ string_of_int n ^ "\n");
  let a = perform (Foo n) in 
  a () 

let send n = 
  match f n with 
  | _ -> ()
  | effect (Foo 0) k -> ()
  | effect (Foo v) k -> continue k (fun () -> f (v-1))

    
let main = send 5 
