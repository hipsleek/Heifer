open Printf

effect Put : int -> unit
effect Get : int

let put v = perform (Put v)
let get () = perform Get

let rec counter (c : int) =
  let i = get ()
  in if (i==0)
      then c
      else (put (i - 1); counter (c + 1))

let _test () = let i = counter 0 in printf "%d\n" i

let read_n_write ()
= let x = get() in
  put(x+1);
  let i = get() in
  printf "%d\n" i

let _ =
  let s = ref 1 in
  match read_n_write () with (* n *)
  | x -> x
  | exception e -> raise e
  | effect Get k -> let i : int = !s in continue k i
  | effect (Put x) k -> s := x; continue k ()
