effect Foo : (int -> unit)

effect A : (int -> unit)

effect B : (int -> unit)

effect O : (int -> unit)



let f () 
(*@ requires emp @*)
(*@ ensures  Foo.Q(Foo 1) @*)
  = perform Foo 1

let o () 
(*@ requires emp @*)
(*@ ensures  O.Q(O 1) @*)
  = perform O 1

let a () 
(*@ requires emp @*)
(*@ ensures A.Q(A 1).B.Q(B 1)  @*)
  = let _ = perform A 1 in perform B 1

let b () 
(*@ requires emp @*)
(*@ ensures A.Q(A 1).B.Q(B 1)  @*)
  = let _ = perform A 1 in perform B 1


let write () : unit
  (*@ requires emp @*)
  (*@ ensures  Foo.A.B.B.B @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->
     continue k (fun _ -> a() )
  | effect A k ->
     continue k (fun _ -> b())
(*
This will stack overflow. 
  | effect A k ->
     continue k (fun _ -> a())
     *)
  | effect B k ->
     continue k (fun _ -> ())
  
  
let main
  (*@ requires emp @*)
  (*@ ensures  Foo.A.B.B.B @*)
  = write ();;



