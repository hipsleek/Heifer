effect Choose : (int * float)

let choose ()
  (*@ requires _^* @*)
  (*@ ensures Choose @*)
= perform Choose

let rec toss n : (string * float) 
  (*@ requires _^* @*)
  (*@ ensures Choose^n @*)
=
  if n = 0 then ("", 1.0)
  else 
    let (a, p) = choose () in 
    let (b, p1) = toss (n-1) in 
    (string_of_int a ^ b, p *. p1)

let all_results () 
(*@ requires emp, eff(m)= _^* -> A  @*)
(*@ ensures A @*)
=
  match toss 3 with
  | v -> [v]
  | effect Choose k -> 
     (continue k (0, 0.3)) @ (continue (Obj.clone_continuation k) (1, 0.7))

let rec pretty_print li : string = 
  match li with 
  | [] -> ""
  | (a, p) :: xs  -> a ^ ", " ^ string_of_float p ^ "\n" ^ pretty_print xs 

let () = 
  print_endline (pretty_print(all_results ()))

