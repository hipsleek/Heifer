effect Open : int -> unit
effect Close: int -> unit

let open_file n
(*@ requires _^* @*)
(*@ ensures Open(n) @*)
= perform (Open n)
