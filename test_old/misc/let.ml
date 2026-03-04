
effect A : unit
effect B : unit
effect C : unit
effect D : unit

let main () =

let f x
  (*@ requires A @*)
  (*@ ensures B @*)
=
  perform B
in

let g x
  (*@ requires C @*)
  (*@ ensures D @*)
=
  perform D
in

  let a =
    if true then f else g
  in
  a ()
