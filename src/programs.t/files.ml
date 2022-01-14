
effect Open : int
effect Close : int -> unit

let open_file ()
  (*@ requires _^* @*)
  (*@ ensures Open @*)
= perform Open

let close_file s
  (*@ requires (_^* ) .Open . ((~Close)^*) @*)
  (*@ ensures Close(s) @*)
= perform (Close s)

let file ()
  (*@ requires emp @*)
  (*@ ensures Open.Close @*)
= let fd = open_file () in
  let fd = open_file () in
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

let file1 ()
  (*@ requires emp @*)
  (*@ ensures _^* @*)
= let fd = open_file () in
  let fd = open_file () in
  close_file fd

let file2 ()
  (*@ requires emp @*)
  (*@ ensures _^* @*)
= let fd = open_file () in
  close_file fd
  (* fails as expected *)
  (* ; close_file fd *)

let file3 ()
  (*@ requires emp @*)
  (*@ ensures _^* @*)
= let fd = open_file () in
  let fd = open_file () in
  close_file fd
  (* fails? *)
  (* ; close_file fd *)

(* but this is ok *)
let file4 ()
  (*@ requires emp @*)
  (*@ ensures _^* @*)
= let fd = open_file () in
  close_file fd;
  let fd = open_file () in
  close_file fd
