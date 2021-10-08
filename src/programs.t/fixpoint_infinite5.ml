effect Send : unit

effect Ready : unit

effect Wait : unit

effect Messenger : (unit -> unit)

let rec until_ready () 
  (*@ requires (_^* ) @*)
  (*@ ensures ((Wait^* ) . Ready) @*)
=
   if true then
     perform Ready
   else
     (perform Wait;
     until_ready ())
    
 let rec send_msgs n 
   (*@ requires (_^* ) @*)
   (*@ ensures (Send^* ) @*)
 =
   if n = 0 then ()
   else
      (
         perform Send; 
         send_msgs (n-1)
      )

 let rec messenger n 
  (*@ requires (_^* ) @*)
  (*@ ensures (((Wait^* ) . Ready).(Send^* )).Messenger. Q(Messenger ()) @*)

  (* if there is a *, the fixpoint won't stop *)
 =
   until_ready ();
   send_msgs n;
   perform Messenger ()

let main 
   (*@ requires (_^* ) @*)
   (*@ ensures (_)^w @*)
= 
   match (messenger 3) with 
   | _ -> ()
   | effect Ready k -> print_string ("[Ready] "); continue k ()
   | effect Send k -> print_string ("[Send] "); continue k ()
   | effect Wait k -> print_string ("[Wait] "); continue k ()
   | effect Messenger k -> 
      (print_string ("[Messenger] "); 
      continue k (fun _ -> messenger 3))