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
= [flip () && flip ()]
  

let all_results () 
(*@ ex i; 
   Norm(i->6, [true;false;false])
@*)
= let i = Sys.opaque_identity (ref 0) in 
  match toss_twice () with
  | v ->  v
  | effect Flip k ->
     i := !i + 1;
     let res1 = (continue (Obj.clone_continuation k) (true)) in  
     i := !i + 1;
     let res2 = (continue k (false)) in 
     res1 @ res2 

let () = 
  List.iter (fun a -> print_endline (string_of_bool a)) (all_results ())
