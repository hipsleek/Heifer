

effect Send : (int -> unit)
effect Done : (unit)

let send m 
(*@ requires _^* @*)
(*@ ensures Send.Q(Send m) @*)
= perform Send m

let server n
(*@ requires _^* @*)
(*@ ensures  (Send^* ).Done @*)
= match send n with
| _ -> perform Done
| effect Send k -> continue k 
    (fun i -> if i = 0 then () 
      	      else send (i-1))


let main 
(*@ requires _^* @*)
(*@ ensures  (Send^* ).Done @*)
= server (-10)


