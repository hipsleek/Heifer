let roll_dice () = 100

let call_ret f = 
  let x = roll_dice () in 
  f x

let x = ref (1)

let cl i = 
  let r = !x in 
  x := r - i; 
  r;;


assert (!x > 0);;
call_ret(cl);;

assert (!x > 0);;  (* the function call is only valid at the first time *)
call_ret(cl);;