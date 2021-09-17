effect Foo : (unit -> int)

let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo ()) @*)
= perform Foo ()
 

