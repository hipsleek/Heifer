let roll_dice () = 100

let call_ret f = 
  let x = roll_dice () in 
  f x

let x = ref (-1)

let cl i = 
  let r = !x in 
  x := i; 
  r;;

(* L1 *)
cl(2);;

assert (!x > 0);;
(* L2: the call here is only valid after L1*)
call_ret(cl);;