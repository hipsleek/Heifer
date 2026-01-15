effect Send : (int -> unit)
effect Done : (unit)

let send n 
(*@ requires (~Done)^* @*)
(*@ ensures Send.Q(Send n) @*)
= perform Send n

let server n
(*@ requires emp @*)
(*@ ensures  (Send^* ).Done @*)
= match send n with
| _ -> ()
| effect Done k -> continue k ()
| effect Send k -> continue k 
  (fun i -> 
    (* Send^*.Done  \/ Send^w  *)
    (* Done \/ (Send)^*.Done \/ Send^w  *)
    if i = 0 then perform Done  
      	    else send (i-1))


let main 
(*@ requires emp @*)
(*@ ensures  (Send.Done) \/ ((Send^* ).Done)  @*)
= server (10)

precondition \phi_pre
postcondition \phi_post

\phi_post -> p100 \phi_post' -> ... p1 -> \phi_post''
\phi_post'' |- \phi_pre  (bug!) 

{n < 0}

let send (n) = 
  if n = 0 then ()
  else send (n-1)

{n < 0}



n >=0 terminating
n < 0 non-terminating. 
 


