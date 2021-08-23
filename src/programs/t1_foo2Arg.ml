effect Foo : (int -> int -> unit)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo 1).Q(Foo 1 2) @*)
  = let a = perform Foo in 
    let b = a 1 in 
    b 2

(*  string * instant
  "a", FOO
  "B"
  *)

let res : unit
  (*@ requires emp @*)
  (*@ ensures  Foo.Goo.Goo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k -> continue k (fun _ _ -> ())
