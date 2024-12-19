effect Foo : (unit -> unit)

effect Goo : (unit -> unit)

effect Open : (unit -> unit)


let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo ()) @*)
= perform Foo ()

let o () 
(*@ requires _^* @*)
(*@ ensures  Open.Q(Open ()) @*)
= perform Open ()

let write () : unit
  (*@ requires (_^* ).Open @*)
  (*@ ensures  (Foo.Goo)^w @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->
     continue k (fun () -> perform Goo ())

  | effect Goo k ->
     continue k (fun () -> perform Foo ());;

let open_file () :unit
  (*@ requires _^* @*)
  (*@ ensures  Open @*)
  = match o () with
  | _ -> ()
  | effect Open k ->
     continue k (fun () -> ());;

let main
  (*@ requires emp @*)
  (*@ ensures  Open.(Foo.Goo)^w @*)
  =
  open_file ();
  write ();;



