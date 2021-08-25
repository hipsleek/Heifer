effect Foo : (unit -> 'a)

let main ()
  (*@ requires emp @*)
  (*@ ensures  Foo @*)
= let f ()
    (*@ requires emp @*)
    (*@ ensures  Foo @*)
  = perform Foo
  in
  f ()
