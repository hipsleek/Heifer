
effect Choose : int

let choose ()
  (*@ requires _^* @*)
  (*@ ensures Choose @*)
= perform Choose

let toss () =
  if choose () = 0
  then if choose () = 0 then "heads, heads" else "heads, tails"
  else "tails"

let all_results m =
  match m () with
  | v -> [v]
  | effect Choose k ->
     (continue k 0) @ (continue (Obj.clone_continuation k) 1)

let () = 
  List.iter print_endline (all_results toss)
