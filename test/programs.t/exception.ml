effect Exc : (unit -> unit)
effect Other : unit

let raise n
(*@ requires (_^* ) @*)
(*@ ensures Exc.Q(Exc ()).Other @*)
= perform Exc ();
  perform Other

let excHandler 
(*@ requires (_^* ) @*)
(*@ ensures Exc @*)
= match raise () with 
| _ -> (* Abandoned code *) perform Other
| effect Exc k -> ()

