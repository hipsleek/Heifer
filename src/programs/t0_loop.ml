effect Foo : (unit -> 'a)


let f () 
  requires emp
  ensures  Foo
= perform Foo ()

let res
  requires emp
  ensures  Foo^*
  =
  match f () with
  | x -> x
  | effect Foo k ->
     continue k (fun () -> perform Foo ())
