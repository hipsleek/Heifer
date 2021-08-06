effect Foo : (unit -> unit)

effect A : (unit -> unit)

effect B : (unit -> unit)

effect O : (unit -> unit)



let f () 
(*@ requires emp @*)
(*@ ensures  Foo @*)
  = perform Foo ()

let o () 
(*@ requires emp @*)
(*@ ensures  O @*)
  = perform O ()

let a () 
(*@ requires emp @*)
(*@ ensures A.B.B  @*)
  = let _ = perform A () in perform B () 

let write () : unit
  (*@ requires emp @*)
  (*@ ensures  Foo.A.B.B @*)
  =
  match f () with
  | x -> ()
  | effect Foo k ->
     continue k (fun () -> a() )
  | effect A k ->
     continue k (fun () -> perform B ())
  | effect B k ->
     continue k (fun () -> ())
  
  
let main
  (*@ requires emp @*)
  (*@ ensures  Foo.A.B.B @*)
  = write ();;



