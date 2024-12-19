
let getAndAdd (i:int ref)
= i := !i + 1

effect E : (int ref * int ref) -> unit 

let two_locations () 
= let i = ref 0 in let j = ref 0 in 
  perform (E(i, j));
  i := !i + 1;
  j := !j + 1

