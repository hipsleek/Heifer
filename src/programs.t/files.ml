
effect Open : int
effect Close : int -> unit

let open_file ()
(*@ requires _^* @*)
(*@ ensures Open @*)
= perform Open

let close_file s
(*@ requires (_^* ) .Open . ((~Close)^*) @*)
(*@ ensures Close @*)
= perform (Close s)

let file ()
(*@ requires emp @*)
(*@ ensures Open.Close @*)
= let fd = open_file () in
  close_file fd

let main ()
  (*@ requires emp @*)
  (*@ ensures Open.Close @*)
=
  match file () with
  | r -> ()
  | effect (Close s1) k ->
    continue k ()
  | effect Open k ->
    continue k 1


