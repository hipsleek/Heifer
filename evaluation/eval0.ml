effect Foo : (unit -> unit)

let f0 () 
(*@ requires _^* @*)
(*@ ensures  Foo.Q(Foo()) @*)
  = perform Foo ()

let f1 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Q(Foo()) @*)
  =
  match f0 () with
  | _ -> perform Foo ()
  | effect Foo k ->  continue k (fun () -> ())

let f2
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Foo.Q(Foo()) @*)
  =
  match f1 () with
  | _ -> perform Foo ()
  | effect Foo k ->  continue k (fun () -> ())

let f3
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Foo.Foo.Q(Foo()) @*)
  =
  match f2 () with
  | _ -> perform Foo ()
  | effect Foo k ->  continue k (fun () -> ())

let f4
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Foo.Foo.Foo.Q(Foo()) @*)
  =
  match f3 () with
  | _ -> perform Foo ()
  | effect Foo k ->  continue k (fun () -> ())

let f5
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Foo.Foo.Foo.Foo.Q(Foo()) @*)
  =
  match f4 () with
  | _ -> perform Foo ()
  | effect Foo k ->  continue k (fun () -> ())

let f6
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Foo.Foo.Foo.Foo.Foo.Q(Foo()) @*)
  =
  match f5 () with
  | _ -> perform Foo ()
  | effect Foo k ->  continue k (fun () -> ())


let f7
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo.Foo.Foo.Foo.Foo.Foo.Foo.Q(Foo()) @*)
  =
  match f6 () with
  | _ -> perform Foo ()
  | effect Foo k -> continue k (fun () -> ())



