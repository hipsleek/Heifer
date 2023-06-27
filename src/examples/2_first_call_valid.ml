let roll_dice () = 100

let call_ret f = 
  let x = roll_dice () in 
  f x

let main_false ()
(*@ Norm(emp, 1) @*)
= let x = ref 2 in

  let cl i =
    let r = !x in
    x := r - i;
    r
  in

  assert (!x=2);
  call_ret cl;
  assert (!x=3);
  (* the function call is only valid at the first time *)
  1
