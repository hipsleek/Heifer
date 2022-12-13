effect Choose : int

let choose ()
  (*@ requires _^* @*)
  (*@ ensures Choose @*)
= perform Choose

let helper v : string = 
  if v = 0 then "head " else "tail "

let rec toss n 
  (*@ requires _^* @*)
  (*@ ensures Choose^n @*)
=
  if n = 0 then ""
  else 
    let a = choose () in 
    helper a ^ toss (n-1)

let all_results m 
(*@ requires emp, eff(m)= _^* -> A  @*)
(*@ ensures A @*)
=
  match m 3 with
  | v -> [v]
  | effect Choose k ->
     (continue k 0) @ (continue (Obj.clone_continuation k) 1)

let () = 
  List.iter print_endline (all_results toss)

