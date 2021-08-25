effect Foo : (unit -> unit)


let f g
(*@ requires eff(g) = emp, true, emp @*)
(*@ ensures  Foo @*)
= perform Foo

let h n
(*@ requires Foo.Q(Foo 1) @*)
(*@ ensures  Foo @*)
= perform Foo ()

let h n
(*@ requires emp, 1 + (2-1) < 1 @*)
(*@ ensures  Foo @*)
= perform Foo ()

let res_f
  (*@ requires emp @*)
  (*@ ensures Foo  @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->
     continue k (fun () -> ())
