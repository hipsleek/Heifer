
let f1 ()
(*@ ex i; Norm(i->[], []) @*)
= let l = ref [] in
  !l

let f2 ()
(*@ ex i; Norm(i->[42], [42]) @*)
= let l = ref [] in
  l := 42 :: !l;
  !l

  (*

ex l. ens l->[] /\ list=l; ex v. req list->v; ens list->v /\ res=v
A * ENS |- REQ * F
A = v=[]
F = emp

      *)


(* 

let cl i 
(*@ 
   ex old; 
   req list -> old ; 
   Norm(list->old @ [i], ())
@*)
= list := !list @ [i];;

let foo closure j = 
(*@ 
   ex new; 
   closure (emp, i, ());
   req list -> new ; 
   Norm(list->new  @ [i+1], ())
@*)
  closure(j);
  list := !list @ [j+1];;


foo (cl) 7;;

assert (!list = [42; 7; 8]);;
(* 
   ex new; closure (emp, i, ()); req list -> new ; Norm(list->new  @ [i+1], ())
~~~>
   ex new; req list -> old ; Norm(list->old @ [7], ()); req list -> new ; Norm(list->new  @ [8], ())
~~~>
   Norm(list->[42, 7, 8], ())
*)

let main = 
  List.map (fun a -> print_endline (string_of_int a)) (!list);;  *)