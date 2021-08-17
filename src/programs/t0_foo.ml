effect Foo : (unit -> 'a)


let f g
(*@ requires eff(g) = emp, true, emp @*)
(*@ ensures  Foo @*)
= perform Foo

let f n
(*@ requires Foo.Q(Foo 1) @*)
(*@ ensures  Foo @*)
= perform Foo 1

let res_f
  (*@ requires emp @*)
  (*@ ensures Foo  @*)
  =
  match f () with
  | x -> x
  | effect Foo k ->
     continue k (fun () -> ())
