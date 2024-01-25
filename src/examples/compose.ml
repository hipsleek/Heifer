
let compose f g x = f (g x)

let compose_pure () 
(*@ ens res=3 @*)
= compose (fun y -> y + 1) (fun z -> z + 2) 0

let f x = x := !x + 1; x

let g x = x := !x + !x; x

let compose_state_1 () 
(*@ ex w; ens w->3/\res=3 @*)
= let x = ref 1 in
  let y1 = compose f g x in
  !y1

let compose_state_2 ()
(*@ ex w; ens w->4/\res=4 @*)
= let y = ref 1 in 
  let y1 = compose g f y in
  !y1
