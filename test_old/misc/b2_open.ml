effect Foo : (unit -> unit)

module A = struct
  let f ()
    (*@ requires emp @*)
    (*@ ensures  Foo @*)
  = perform Foo
end

open A

let main ()
  (*@ requires emp @*)
  (*@ ensures  Foo @*)
= f ()
