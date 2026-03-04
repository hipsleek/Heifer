effect Done : unit
effect Send : unit

let rec send n 
(*@ requires  _^* @*)
(*@ ensures	 (Send^* .Done)\/(Send^w)  @*)
= 
  if n=0 
  then perform Done
  else 
    (perform Send;
    send (n-1))

