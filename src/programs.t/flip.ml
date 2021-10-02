
effect Choose : int

let choose ()
  (*@ requires _^* @*)
  (*@ ensures Choose @*)
= perform Choose

let toss () 
(*@ requires _^* @*)
  (*@ ensures (Choose.Choose) \/ Choose @*)
=
  let a = choose () in 
  if a = 0
  then let b = choose () in if b  = 0 then "heads, heads" else "heads, tails"
  else "tails"

(*SYH: debug the if constructs*)

let all_results m =
  match m () with
  | v -> [v]
  | effect Choose k ->
     (continue k 0) @ (continue (Obj.clone_continuation k) 1)

let () = 
  List.iter print_endline (all_results toss)
