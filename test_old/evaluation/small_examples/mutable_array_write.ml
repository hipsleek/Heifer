effect Write : int -> int

let write x
(*@ 
  ex ret;
  Write(emp, x, ret);
  Norm(emp, ret)   
@*)
= perform (Write x)

let array_update ()
(*@
  ex i;
  Norm(i->1, 1)
@*)
= 
  let g = [| 2; 3; 4; 5 |] in
  match write 1 with
  | v -> g.(0)
  | effect (Write x) k -> g.(0) <- x; (continue k ())
  print_string (string_of_int g.(0))
  let i = g.(0)