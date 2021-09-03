effect Foo : (int -> int)
effect Goo : (int -> int)

let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo 1).Goo @*)
= let a = perform Foo in 
  let b = perform Goo in 
  b 1 

