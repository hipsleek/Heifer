effect Send : unit
effect Ready: unit
effect Wait : unit
effect Done : (unit -> unit)

let rec until_ready ()
  (*@ requires _^* @*)
  (*@ ensures Wait^* . Ready @*)
=
  if nondet_bool () then
    perform Ready
  else
    (perform Wait;
     until_ready ())

let rec send_msgs n
   (*@ requires _^* @*)
   (*@ ensures Send^* @*)
=
  if n = 0 then ()
  else
    (perform Send;
     send_msgs (n-1))

let messenger n
  (*@ requires _^* @*)
  (*@ ensures Wait^* . Ready. Send^* . Done. Q(Done ()) @*)
=
   until_ready ();
   send_msgs n;
   let g = perform Done in
   g ()

let main ()
   (*@ requires emp @*)
   (*@ ensures (Wait^* . Ready . Send^* . Done)^w @*)
=
  match (messenger 3) with
  | _ -> ()
  | effect Ready k | effect Send k | effect Wait k ->
    continue k ()
  | effect Done k ->
    continue k (fun _ -> messenger 3)
