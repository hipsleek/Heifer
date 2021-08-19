effect Foo : (unit -> 'a)


let f ()
(*@ requires emp @*)
(*@ ensures  Foo @*)
= perform Foo

let g ()
(*@ requires emp @*)
(*@ ensures  Foo @*)
= f ()