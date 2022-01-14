effect Send : (int -> unit)
effect Done : (unit)

let send n 
(*@ requires (~Done)^* @*)
(*@ ensures Send.Q(Send n) @*)
= perform Send n

let server n
(*@ requires _^* @*)
(*@ ensures  (Send^* ).Done @*)
= match send n with
| _ -> ()
| effect Done k -> continue k ()
| effect Send k -> continue k 
  (fun i -> if i = 0 then perform Done  
      	    else send (i-1))

(*
Send.Done \/ Send.Q(Send n)

Send. (Done \/ Send.Q(Send n))

*)

let main 
(*@ requires _^* @*)
(*@ ensures  (Send.Done) \/ ((Send^* ).Done)  @*)
= server (10)
 


