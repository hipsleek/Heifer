effect Foo : (unit -> int)
effect Goo : (int -> int)

let f () d
(*@ requires emp, eff(d) = emp -> emp @*)
(*@ ensures  Foo.Q(Foo ()).Goo @*)
= let _a = perform Foo () in
  let b = perform Goo in
  b




let res_f
  (*@ requires emp @*)
  (*@ ensures Foo.(Goo^w)   @*)
  =
  match (f ()) with
  | x -> x
  | effect Foo k ->
      continue k (fun _ -> perform Goo 1 )
  | effect Goo k ->
      continue k (fun _ -> perform Goo 1;)

(*  ensures Foo.Q(Foo()) where Q(Foo_) = Foo *)
