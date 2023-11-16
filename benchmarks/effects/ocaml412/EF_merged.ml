effect Put : int -> unit
effect Get : int
effect Exchange : int -> int

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

let read_n_write1 ()
(*@  ex x; Get(emp, x);  ex r1; Put(emp, x+1, r1); ex r; Put(emp, x+2, r); ex i; Get(emp, i); Norm(emp, i+2) @*)
= let x = get() in
  put(x+1);
  put(x+2);
  let i = get() in
  i +2


let _test () 
(*@  ex s;  Norm(s->2, 2) @*)
= let s = ref 1 in
  match read_n_write () with (* n *)
  | x -> x
  | exception e -> raise e
  | effect Get k -> let i = !s in continue k i
  | effect (Put x) k -> s := x; continue k ()

let _test1 () 
(*@  ex s;  Norm(s->3, 5) @*)
= let s = ref 1 in
  match read_n_write1 () with (* n *)
  | x -> x
  | exception e -> raise e
  | effect Get k -> let i = !s in continue k i
  | effect (Put x) k -> s := x; continue k ()

let shoud_be_wrong__test () 
(*@  ex s;  Norm(s->2, 1) @*)
= let s = ref 1 in
  match read_n_write () with (* n *)
  | x -> x
  | exception e -> raise e
  | effect Get k -> let i = !s in continue k i
  | effect (Put x) k -> s := x; continue k ()

let shoud_be_wrong__test1 () 
(*@  ex s;  Norm(s->1, 5) @*)
= let s = ref 1 in
  match read_n_write1 () with (* n *)
  | x -> x
  | exception e -> raise e
  | effect Get k -> let i = !s in continue k i
  | effect (Put x) k -> s := x; continue k ()



let exchange (m:int)
(*@ ex r; Exchange(emp, m, r); Norm(res=r) @*)
= perform (Exchange m)

let exc_handler (l:int ref) (new_v:int)
(*@ ex z; req l->z; Norm(l->new_v, z) @*)
=  match exchange new_v with
  | x -> x
  | exception e -> raise e
  | effect (Exchange n) k ->
     let old_v = !l in
     l := n;
     continue k old_v

let testEXG () 
(*@ ex l;  Norm(l->10, 5) @*)
= let l = ref 5 in
  let i = exc_handler l 10 in
  i

let testEXG1 () 
(*@ ex l;  Norm(l->100, 5) @*)
= let l = ref 5 in
  let i = exc_handler l 10 in
  let i1 = exc_handler l 100 in
  i

let shoud_be_wrong_testEXG () 
(*@ ex l;  Norm(l->10, 3) @*)
= let l = ref 5 in
  let i = exc_handler l 10 in
  i

let shoud_be_wrong_testEXG1 () 
(*@ ex l;  Norm(l->900, 5) @*)
= let l = ref 5 in
  let i = exc_handler l 10 in
  let i1 = exc_handler l 100 in
  i
