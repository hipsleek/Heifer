effect Exc : int -> unit

let raise n
  (*@ requires _^* @*)
  (*@ ensures Exc @*)
= perform (Exc n);
  perform (Exc n)

let excHandler 
  (*@ requires _^* @*)
  (*@ ensures Exc @*)
= match raise 404 with 
  | _ -> ()
  | effect (Exc code) k -> ()