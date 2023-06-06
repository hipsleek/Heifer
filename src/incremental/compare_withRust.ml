
let list = ref [];;

list := !list @ [42];;


let cl i 
(*@ 
   Norm(list->old(list) @ [i], ())
@*)
= list := !list @ [i];;

let foo closure i = 
(*@ 
   closure (emp, i, ());
   Norm(list->old(list) @ [i+1], ())
@*)
  closure(i);
  list := !list @ [i+1];;


foo (cl) 7;;
(* 
closure (emp, i, ()); Norm(list->old(list) @ [i+1], ())
~~~>
Norm(list->old(list) @ [i], ()); Norm(list->old(list) @ [i+1], ()) 
~~~>
Norm(list->old(list) @[i] @ [i+1], ())
*)


let main = 
  List.map (fun a -> print_endline (string_of_int a)) (!list);; 