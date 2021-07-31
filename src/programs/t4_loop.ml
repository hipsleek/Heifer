effect Foo : (unit -> unit)

effect Goo : (unit -> unit)

effect Open : (unit -> unit)


let f () 
(*@ requires emp @*)
(*@ ensures  Foo @*)
  = perform Foo ()

let o () 
(*@ requires emp @*)
(*@ ensures  Open @*)
  = perform Open ()

let write () : unit
  (*@ requires Open @*)
  (*@ ensures  (Foo.Goo)^w @*)
  =
  match f () with
  | x -> ()
  | effect Foo k ->
     continue k (fun () -> perform Goo ())

  | effect Goo k ->
     continue k (fun () -> perform Foo ());;

let open_file () :unit =
  (*@ requires emp @*)
  (*@ ensures  Open @*)
  match o () with
  | x -> ()
  | effect Open k ->
     continue k (fun () -> ());;

let main = 
  (*@ requires emp @*)
  (*@ ensures  Open.(Foo.Goo)^w @*)
  open_file ();
  write ();;



