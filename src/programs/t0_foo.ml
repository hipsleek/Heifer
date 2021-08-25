effect Foo : (unit -> unit)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo @*)
= perform Foo

let res_f () 
  (*@ requires emp @*)
  (*@ ensures Foo  @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->
     continue k (fun () -> ())
