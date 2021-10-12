effect Exc : int -> unit
effect Foo : unit

let raise n
  (*@ requires _^* @*)
  (*@ ensures Exc @*)
= perform (Exc n);
  perform Foo

let excHandler 
  (*@ requires _^* @*)
  (*@ ensures Exc @*)
= match raise 404 with 
  | _ -> ()
  | effect (Exc code) k -> ()