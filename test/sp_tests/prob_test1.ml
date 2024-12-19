effect Choose : (int list * float)

let choose ()
  (*@ requires (true, _^* ) @*)
  (*@ ensures (true, Choose) @*)
= perform Choose

let flip_compose (a, b) (c, d) = 
  (List.append a c, b*.d) 

    (*@ requires (true, _^* ) @*)
  (*@ ensures (n=0, Norm([], 1.0) \/ n!=0, ) @*)

let rec pretty_print li : string = 
  match li with 
  | [] -> ""
  | (a, p) :: xs  -> (List.fold_left (fun acc i -> acc ^ string_of_int i) "" a) ^ ", " ^ string_of_float p ^ "\n" ^ pretty_print xs 


let rec toss n : (int list * float)
= if n == 0 then ([], 1.0)
  else flip_compose (choose ()) (toss (n-1)) 

let all_results () 
= match toss 3 with
  | v -> [v]
  | effect Choose k -> 
    List.append 
      (continue k ([0], 0.3)) 
      (continue (Obj.clone_continuation k) ([1], 0.7))

let main = print_endline (pretty_print(all_results () ))


