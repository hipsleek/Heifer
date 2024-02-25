effect Read : int 
effect Write : int -> unit 
effect Exchange: int -> int


let read () 
(*@ ex ret; Read(emp, ret); Norm(emp, ret) @*)
= perform Read


let write n 
(*@ ex ret; Write(emp, n,  ret); Norm(emp, ret) @*)
= perform (Write n)


let read_n_write ()
(*@ ex r1;   Read(emp, r1); 
    ex n r2; Write(n=r1+1, n,  r2); 
    ex ret; Read(emp, ret); Norm(res=ret, res) @*)
= let x = read () in 
  write(x+1); (* the Write effect returns () *)
  read ()


(* Figure 38 *)
let state_handler () 
(*@ ex ret i; Norm(i->1/\ret=1, ret) @*)
= let i = ref 0 in 
  match read_n_write () with 
  | v -> v 
  | effect Read k -> resume k !i 
  | effect (Write v) k -> i := v; resume k ()


(* Figure 39 *)
let write_handler j  
(*@ ex r1;   Read(emp, r1); 
    ex r2;   req j-> r2; ens j-> r1+1; 
    ex res r3; Read(emp, r3); Norm(res=r3, res) @*)
= match read_n_write () with
  | v -> v 
  | effect (Write v) k -> j := v; resume k ()


(* Figure 39 *)
let read_handler  ()
(*@ ex ret i; Norm(i->1/\ret=1, ret) @*)
= let i = ref 0 in 
  match (write_handler i) with
  | v -> v 
  | effect Read k -> resume k !i


let exchange (m:int)
(*@ ex ret; Exchange(emp, m, ret); Norm(emp, ret) @*)
= perform (Exchange m)

  
(* Figure 40 *)
let exc_handler (l) (new_v:int)
(*@ ex old; req l-> old ; ens l-> new_v; Norm (res=old, res)   @*)
= match exchange new_v with 
  | v -> v 
  | effect (Exchange n) k -> 
      let old = !l in 
      l := n; 
      resume k old

(* More monad examples *)
(* ASK DARIUS : the enatilment checking does not terminate *)
let test1 ()
(* ex r1; Read(emp, r1); 
    ex r2 r3; Write(r2=r1+1, (r2), r3); 
    ex r4; Read(emp, r4); 
    ex r5 r6; Write(r5=r4+1, (r5), r6); 
    ex r7; Read(emp, r7); Norm (res=r7, res)  *)
= 
  let x = read () in 
  write (x+1);
  let z = read () in 
  write (z+1);
  read ()

let test2 ()
(* ex r1; Read(emp, r1); 
    ex r2 r3; Write(r2=r1+1, (r2), r3); 
    ex r4; Read(emp, r4); 
    ex r7; Read(emp, r7); Norm (res=r7, res)  *)
= 
  let x = read () in 
  write (x+1);
  let z = read () in 
  read ()

let handler1 () 
(*@ ex i; Norm(i->2,  3) @*)
= let i = ref 0 in 
  match test1 () with 
  | v -> v + 1
  | effect Read k -> resume k !i 
  | effect (Write v) k -> i := v; resume k ()

let handler2 () 
(*@ ex i; Norm(i->1,  6) @*)
= let i = ref 0 in 
  match test2 () with 
  | v -> v + 5
  | effect Read k -> resume k !i 
  | effect (Write v) k -> i := v; resume k ()


let handler3 () 
(*@ ex i; Norm(i->1,  2) @*)
= let i = ref 0 in 
  match read_n_write () with 
  | v -> v + 1
  | effect Read k -> resume k !i 
  | effect (Write v) k -> i := v; resume k ()

let handler4 () 
(*@ ex i res; Norm(i->3 /\ res=4,  res) @*)
= let i = ref 0 in 
  match read_n_write () with 
  | v -> v + 1
  | effect Read k -> resume k (!i + 1)
  | effect (Write v) k -> i := v + 1; resume k ()
