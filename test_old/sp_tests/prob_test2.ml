effect Choose : (int list * float)

let choose ()
  (*@ requires (true, _^* ) @*)
  (*@ ensures (true, Choose) @*)
= perform Choose

let flip_compose (a, b) (c, d) = 
  (List.append a c, b*.d) 

let rec toss n : (int list * float)
  (*@ requires (n >=0 , _^* ) @*)
  (*@ ensures (true, Choose^n ) @*)
= if n == 0 then ([], 1.0) 
  else 
    flip_compose (choose ()) (toss (n-1))
    
let toss_const () : (int list * float) 
  (*@ requires (n >=0 , _^* ) @*)
  (*@ ensures (true, Choose ) @*)
= 
  let c1 = choose () in 
  let c2 = choose () in 
  let c3 = choose () in 
  let r1 = flip_compose c1 ([], 1.0) in 
  let r2 = flip_compose c2 r1 in 
  flip_compose c3 r2

let rec pretty_print li : string = 
  match li with 
  | [] -> ""
  | (a, p) :: xs  -> (List.fold_left (fun acc i -> acc ^ string_of_int i) "" a) ^ ", " ^ string_of_float p ^ "\n" ^ pretty_print xs 

let all_results () 
(*@ requires emp, eff(m)= _^* -> A  @*)
(*@ ensures A @*)
=
  match toss_const () with
  | v -> [v]
  | effect Choose k -> 
    List.append (continue k ([0], 0.3)) (continue         (Obj.clone_continuation k) ([1], 0.7))


let main = print_endline (pretty_print(all_results () ))


