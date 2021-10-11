effect Done : (unit -> unit)

effect Send : unit

let rec send n 
(*@ requires  emp @*)
(*@ ensures	 (_^* . Done) 
          \/  (Send^w)  @*)
= 
	if (n=0) then  perfrom Done () 
	else 
		perfrom Send;
		send (n-1)
