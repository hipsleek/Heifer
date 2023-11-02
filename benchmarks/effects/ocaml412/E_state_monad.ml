effect Put : int -> unit
effect Get : int

let put v 
(*@ ex r; Put(emp, v, r); Norm(res=r) @*)
= perform (Put v)


let get () 
(*@ ex r; Get(emp, r); Norm(res=r) @*)
= perform Get

let rec counter (c : int) 
(*@  ex i; Get(emp, i); Norm(i=0, c)
  \/ ex i; Get(emp, i); Norm(~i=0, i);  ex r; Put(emp, i-1, r); counter(c+1, res) @*)
=
  let i = get () in 
  if (i==0) then c
  else (put (i - 1); counter (c + 1))

let read_n_write ()
(*@  ex x; Get(emp, x);  ex r; Put(emp, x+1, r); ex i; Get(emp, i); Norm(emp, i) @*)
= let x = get() in
  put(x+1);
  let i = get() in
  i 

let _test () 
(*@  ex s;  Norm(s->2, 2) @*)
= let s = ref 1 in
  match read_n_write () with (* n *)
  | x -> x
  | exception e -> raise e
  | effect Get k -> let i = !s in continue k i
  | effect (Put x) k -> s := x; continue k ()
