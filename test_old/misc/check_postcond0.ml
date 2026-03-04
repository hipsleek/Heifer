
effect A : unit
effect B : unit

let rec f g
  (*@ requires A, eff(g)= (_^* ) ->  (Update^* ).(Exc \/ emp)  @*)
  (*@ ensures emp, eff(g)= (_^* ) ->  (Update^* ).(Exc \/ emp) @*)
=
  ()

