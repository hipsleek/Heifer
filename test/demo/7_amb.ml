(* McCarthy's locally angelic choice operator (angelic modulo nontermination). *)
(* The following examples are adapted from Oleg Kiselyov
   "Non-deterministic choice amb"
   (c.f. https://okmij.org/ftp/ML/ML.html#amb) *)

effect Choose : (unit -> bool) list -> bool
effect Success : int -> unit 
effect Failure : int -> int 

let rec iter (f)  (xs) 
(*@ ens xs=[]/\res=(); Norm(emp, res) 
\/ 
    ex t; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; 
    ex r1; f(h, r1); 
    ex r2; iter(f, t, r2); Norm(res=r2)    
 @*)
= match xs with
  | [] -> ()
  | h::t -> f h; iter f t

(*@ predicate h (r) = 
   Norm (head_r=false) \/ Norm (head_r=true) @*)

(*@ predicate containRetTrue (xs, c, r) = 
   ex r; Norm(is_nil(xs)=true/\res=r /\ r=false/\ c =0 ) 
\/ ex r1 h t r; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true;  Norm(c = 1 /\ head_r=true /\ res=r /\ r=true)
\/ ex r1 h t; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; 
   Norm(head_r=false); ex r c'; containRetTrue (t,c',r) ; Norm(c = c'+1 /\ res=r)  @*)

let helperk hh 
(*@ ex hret; try ex hr2; continue_syh  (k, head_r, hr2); ex hr3; Success(emp, hr2, hr3)
    catch {
      x ->  Norm(res=()) 
    | (Success x) -> ex hkr; Success(emp, x, hkr) 
    | (Failure x) -> Norm(res=())  
    }[hret] @*)
= match
    (*let k = Obj.clone_continuation k in*)
    let r1 = h () in 
    let temp = continue_syh k (head_r) in 
    perform (Success (temp))
  with
  | effect (Success x) k -> perform (Success (x))
  | effect (Failure x) k -> ()
  | x -> () 
   
let aux k xs 
(*@ ex r; Failure(xs=[], (404), r) \/ ex hr; try 
 ex h t hret; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; ex hret; 
    try ex hr2; continue_syh (k, head_r, hr2); ex hr3; Success(emp, hr2, hr3)
    catch {
      x ->  Norm(res=()) 
    | (Success x) -> ex hkr; Success(emp, x, hkr)
    | (Failure x) -> Norm(res=())  
    }[hret]
; ex r2; iter(helperk, t, r2); ex r; Failure(emp, (404), r) 
 catch {
    x -> ens res=x 
  | (Success r) -> ens res=r 
 }[hr]  @*)
= 
  match iter (helperk) xs; perform (Failure 404) with 
  | effect (Success r) k1 -> r
  | x -> x  



let amb (xs) counter : bool
(*@ ex r; Choose(emp, (xs), r); ex x; req counter->x; Norm(counter->x+1 /\ res = r) @*)
= let b = perform (Choose xs) in counter := !counter +1; b


let m xs counter
(*@ ex r1; Choose(emp, (xs), r1); ex x r; req counter->x; Norm(counter->x+1 /\ r1= true /\ res =r /\ r=7 ) 
 \/ ex r1; Choose(emp, (xs), r1); ex r2 x;req counter->x; Failure(counter->x+1 /\r1=false, 500, r2) @*)
= if amb xs counter then 7 
  else 
    perform (Failure 500)


let handle (xs) counter 
(*@ 
ex v1308; Failure(xs=[], (404), v1308); ens res=v1308 \/ 
ex v1311; req counter->v1311; ens counter->(v1311+1)/\is_cons(xs)=true/\head_r=true/\res=7 \/ 
ex t v1230 v1268 v1269 v1270; req counter->v1230/\(v1230+1)=v1268; ens tail(xs)=t/\is_cons(xs)=true/\head_r=false/\v1268=(v1230+1); containRetTrue(t, v1269, v1270); ens counter->(v1268+v1269)/\v1270=true/\res=7 \/ 
ex t v1230 v1273 v1274 v1275; req counter->v1230/\(v1230+1)=v1273; ens tail(xs)=t/\is_cons(xs)=true/\head_r=false/\v1273=(v1230+1); containRetTrue(t, v1274, v1275); ex v1226; Failure(counter->(v1273+v1274)/\v1275=false, (500), v1226); ens res=v1226
@*)
(* 
ex r c a r1; req counter -> a; containRetTrue (xs, c, r1); ens counter->a+c /\ r1 = true /\ res = r /\ r=7    
\/ ex r c a r1; req counter -> a; containRetTrue (xs, c, r1); Failure(counter->a+c /\r1=false, 500, r) *)
= match m xs counter with
  (* try-catch lemma defined here *)
  (*@   try ex t r;  iter(helperk, t,r) # ex r200; Failure(emp, (404), r200) catch 
     =  ex r c a r1; req counter -> a; containRetTrue (t, c, r1); ens counter->a+c /\ r1 = true /\ res=7 
     \/ ex r c a r1; req counter -> a; containRetTrue (t, c, r1); Failure(counter->a+c /\r1=false, 500, r)
  @*) 
  | x -> x
  | effect (Choose xs) k -> aux k xs
   
(*
let branch_example_generic (xs: (unit -> bool) list) counter : int
= handle xs counter

let _ =
  let counter  = ref 0 in
  let v = branch_example_generic [(fun () -> false ); (fun () -> false); (fun () -> true); (fun () -> false)] counter in
  Printf.printf "(%d)\n%!" v;
  Printf.printf "(counter = %d)\n%!" !counter
*)