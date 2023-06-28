
let compose f g x = f (g x)

let f x = x := !x + 1; x

let g x = x := !x + !x; x

let caller1 () 
(*@ ex w; Norm(w->3, 3) @*)
= let x = ref 1 in
  let y1 = compose f g x in
  !y1

let caller2 ()
(*@ ex w; Norm(w->4, 4) @*)
= let y = ref 1 in 
  let y1 = compose g f y in
  !y1
