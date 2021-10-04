
effect Open : int
effect Close : int -> unit

let open_file ()
  (*@ requires _^* @*)
  (*@ ensures Open @*)
= perform Open

let close_file s
  (*@ requires Open @*)
  (*@ ensures Close @*)
= perform (Close s)

let f ()
  (*@ requires emp @*)
  (*@ ensures Open.Close @*)
=
  let fd = open_file () in
  close_file fd

let main ()
  (*@ requires emp @*)
  (*@ ensures Open.Close @*)
=
  match f () with
  | r -> ()
  | effect (Close s1) k ->
    continue k ()
  | effect Open k ->
    continue k 1

let () = main ()
