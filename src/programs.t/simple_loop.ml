
effect A : unit

let rec f ()
  (*@ requires _^* @*)
  (*@ ensures A^w @*)
=
  perform A; f ()

let rec g n
  (*@ requires _^* @*)
  (*@ ensures A^* @*)
=
  match n with
  | 0 -> ()
  | _ ->
    perform A;
    g (n - 1)

let main ()
  (*@ requires emp @*)
  (*@ ensures A^w @*)
=
  match f () with
  | x -> x
  | effect A k -> continue k ()

let () = main ()
