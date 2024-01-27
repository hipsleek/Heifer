
let compose f g x = f (g x)

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

let compose_shared_1 ()
(*@ ex w; ens w->4/\res=4 @*)
= let y = ref 1 in
  let f x = y := !y + 1; x in
  let g x = y := !y + !y; x in
  let _ = compose g f 1 in
  !y

let compose_shared_2 ()
(*@ ex w; ens w->3/\res=3 @*)
= let y = ref 1 in
  let f x = y := !y + 1; x in
  let g x = y := !y + !y; x in
  let _ = compose f g 1 in
  !y
