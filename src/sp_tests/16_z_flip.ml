effect Flip : bool

let flip ()
(*@ ex ret; 
   Flip(emp, ret);
   Norm(emp, ret)
@*)
= perform Flip

let toss_twice () 
(*@ ex ret ret1; 
   Flip(emp, ret);
   Flip(emp, ret1);
   Norm(emp, [ret; ret1])
@*)
= 
   let a = flip () in 
   let b = flip () in 
   [a&&b]
  

let all_results () 
(*@ ex i; 
   Norm(i->6, [true;false;false])
@*)
= let i = Sys.opaque_identity (ref 0) in 
  let temp = (match toss_twice () with
  | v ->  v
  | effect Flip k ->
     i := !i + 1;
     let res1 = (continue (Obj.clone_continuation k) (false)) in  
     i := !i + 1;
     let res2 = (continue k (true)) in 
     res1 @ res2 ) in 
   print_endline (string_of_int (!i)); 
   temp

let () = 
  List.iter (fun a -> print_endline (string_of_bool a)) (all_results ())
