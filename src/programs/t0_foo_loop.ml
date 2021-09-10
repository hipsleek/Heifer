effect Foo : (int -> int)
effect Goo : (int -> int)

let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo 1).Goo.Q(Goo 1) @*)
= let _ = perform Foo in 
  let b = perform Goo in 
  b 

  

(*
let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(\ i -> Goo.Q (\ i2 -> []). @*)
= let a = perform Foo 1 in 
  let b = perform Goo in 
  b 2


let f () :: Int
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo 1).Goo.Q(Goo 1) @*)
= let C1 = perform Foo in
  let a  = C1 1 in
  let C2 = perform Goo in 
  C2 1)

let res_f
  (*@ requires emp @*)
  (*@ ensures Foo.(Goo^w)   @*)
  =
  match (f ()) with
  | x -> x
  | effect Foo k ->
      continue k ( 1 )
  | effect Goo k ->
      continue k (fun _ -> perform Goo 1;)
      *)

(*  ensures Foo.Q(Foo()) where Q(Foo_) = Foo *)