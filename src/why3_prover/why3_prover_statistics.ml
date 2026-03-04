let smt_time = ref 0.0

let reset_statistics () = smt_time := 0.0

let current_time = Unix.gettimeofday

let get_smt_time () = !smt_time

let add_smt_time t = smt_time := !smt_time +. t
