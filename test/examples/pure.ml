
let [@pure] hello (x:int) : int = x + 1

let pure_hello ()
(*@ ens res=hello(2) @*)
= 3
