effect Exchange: int -> int

let x = Sys.opaque_identity (ref 11) 

let exchange (m:int)
(*@  requires (true, emp, ret)   @*)
(*@  ensures (true, Exchange (m), Exchange(m)?)   @*)
= let res = perform (Exchange m) in 
  res

let exchange_hanlder (old:int) (n:int)
(*@  requires (true, emp, ret)   @*)
(*@  ensures (true, {x->n}, old)   @*)
= match exchange n with 
  | v -> v 
  | effect (Exchange v) k -> 
    x := v; continue k old
