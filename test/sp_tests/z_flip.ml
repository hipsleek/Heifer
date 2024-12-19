effect Choose : int

let choose ()
  (*@ requires _^* @*)
  (*@ ensures Choose @*)
= perform Choose

let helper v : string = 
  if v = 0 then "head " else "tail "


let rec toss n : string 
  (*@ requires _^* @*)
  (*@ ensures Choose^n @*)
=
  if n = 0 then ""
  else 
    let a = choose () in 
    helper a ^ toss (n-1)

let all_results () : string list 
(*@ requires emp, eff(m)= _^* -> A  @*)
(*@ ensures A @*)
=
  let i = Sys.opaque_identity (ref 0) in 
  match toss 3 with
  | v -> [v]
  | effect Choose k ->
     (continue k (i:= !i+1; 0)) @ 
     (continue (Obj.clone_continuation k) (i:= !i+1;1))

let () = 
  List.iter print_endline (all_results ())

