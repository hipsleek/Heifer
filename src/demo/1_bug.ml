effect Read : int 
effect Write : int -> unit 
effect Exchange: int -> int


let read () 
(*@ ex ret; Read(emp, ret); Norm(emp, ret) @*)
= perform Read


let write n 
(*@ ex ret; Write(emp, n,  ret); Norm(emp, ret) @*)
= perform (Write n)


(* ASK DARIUS : the enatilment checking does not terminate test1 *)
let test1 ()
(* ex r1; Read(emp, r1); 
    ex r2 r3; Write(r2=r1+1, (r2), r3); 
    ex r4; Read(emp, r4); 
    ex r5 r6; Write(r5=r4+1, (r5), r6); 
    ex r7; Read(emp, r7); Norm (res=r7, res)  @*)
= 
  let x = read () in 
  write (x+1);
  let z = read () in 
  write (z+1);
  read ()

(***************************************)
(******* existential functions **************)
(* ASK DARIUS :  the verification of aux shoudl go through ! *)


effect Choose : (unit -> bool) list -> bool
effect Success : int -> unit 
effect Failure : int -> int 

let rec iter (f)  (xs) 
(*@ ens xs=[]/\res=(); Norm(emp, res) 
\/ 
    ex h t; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; 
    ex r1; f(h, r1); 
    ex r2; iter(f, t, r2); Norm(res=r2)    
 @*)
= match xs with
  | [] -> ()
  | h::t -> f h; iter f t

(*@ predicate containRetTrue (xs, c, r) = 
   ex r; Norm(is_nil(xs)=true/\res=r /\ r=false/\ c =0 ) 
\/ ex r1 h t r; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; h((), r1); Norm(c = 1 /\ r1=true /\ res=r /\ r=true)
\/ ex r1 h t; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; h((), r1); 
   Norm(r1=false); ex r c'; containRetTrue (t,c',r) ; Norm(c = c'+1 /\ res=r) 
@*)

let helperk h
(*@ 
    ex hret; 
    try ex hr1; h((), hr1); ex hr2; continue(k, hr1, hr2); ex hr3; Success(emp, hr2, hr3)
    catch {
      x ->  Norm(res=()) 
    | (Success x) -> ex hkr; Success(emp, x, hkr); Norm (res=hkr) 
    | (Failure x) -> Norm(res=())  
    }[hret]
@*)
= match
    let k = Obj.clone_continuation k in
    let r1 = h () in 
    let temp = continue k (r1) in 
    perform (Success (temp))
  with
  | effect (Success x) k -> perform (Success (x))
  | effect (Failure x) k -> ()
  | x -> () 

let aux k xs 
(*@ 
 ex r; Failure(xs=[], (404), r) 
\/ 
ex hr; 
try 
 ex h t hret; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true;     
    try ex hr1; h((), hr1); ex hr2; continue(k, hr1, hr2); ex hr3; Success(emp, hr2, hr3)
    catch {
      x ->  Norm(res=()) 
    | (Success x) -> ex hkr; Success(emp, x, hkr); Norm (res=hkr) 
    | (Failure x) -> Norm(res=())  
    }[hret]
;
 ex r2; iter(helperk, t, r2); ex r; Failure(emp, (404), r) 
 catch {
    x -> ens res=x 
  | (Success r) -> ens res=r 
 }[hr] ;
 ens res= hr
@*)
= 
  match iter (helperk) xs; perform (Failure 404) with 
  | effect (Success r) k1 -> r
  | x -> x  

