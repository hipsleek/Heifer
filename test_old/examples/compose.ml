
let compose f g x = f (g x)

let compose_pure () 
(*@ ens res=3 @*)
= compose (fun y -> y + 1) (fun z -> z + 2) 0
