(* McCarthy's locally angelic choice operator (angelic modulo nontermination). *)

effect Choose : (unit -> bool) list -> bool
effect Success : int -> unit 
effect Failure : int -> int 

let amb (xs : (unit -> bool) list) : bool
(*@ ex r; Choose(emp, (xs), r) @*)
= perform (Choose xs)

let rec iter (f:((unit -> bool) -> unit))  (xs:(unit -> bool) list) :  unit
(*@ Norm(is_nil(xs)=true/\res=()) 
\/ ex r1 h t; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; f(h, r1); ex r2; iter(f, t, r2); Norm(res=r2)
@*)
= match xs with
  | [] -> ()
  | h::t -> f h; iter f t


let m xs 
(*@ ex r1 ; Choose(emp, (xs), r1); Norm(r1= true /\ res =7 ) 
\/ ex r1 ; Choose(emp, (xs), r1); ex r2; Failure(r1=false, 500, r2); Norm(res =r2 ) @*)
= if amb xs then 7 else perform (Failure 500)


(*@ predicate containRetTrue (xs) = 
   Norm(is_nil(xs)=true/\res=false ) 
\/ ex r1 h t; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; h((), r1); Norm(r1=true /\ res=true)
\/ ex r1 h t; ens head(xs)=h/\tail(xs)=t/\is_cons(xs)=true; h((), r1); Norm(r1=false); ex r; containRetTrue (t, r) ; Norm(res=r)
@*)


(*
let handle (xs:(unit -> bool) list) : int 
(*@ 
  try m() with 
  {x -> Norm(res=x); 
  (Choose xs) k -> 
    try 
        req xs=[]; Failure(emp, -1, r)
        \/
        ex temp; req xs=h::t; 
        try (h(emp, (), r1); continue(emp, r1, temp)); Success(emp, temp, r2)
        with 
          {x -> Norm(res=()); 
           (Success x) k -> Success (emp, x, res); 
           (Failure x) k -> Norm(res=())}
    with 
    {x -> Norm(res=x)
    (Success x) k -> Norm(res=x)}
  }
@*)
= match (m xs) with
  | x -> x
  | effect (Choose xs) k ->
  match 
    iter
      (fun h ->
        match
          let k = Obj.clone_continuation k in
          let (temp:int) = continue k (h ()) in
          perform (Success (temp))
        with
        | effect (Success x) k -> perform (Success (x))
        | effect (Failure x) k -> ()
        | x -> ()
      ) xs;
    perform (Failure 404)
  with 
  | effect (Success r) k -> r
  | x -> x  





let branch_example_generic (xs: (unit -> bool) list) : int
(*@ ex r; req containRetTrue (xs, true); ens res = r /\ r=7 
    ex r; req containRetTrue (xs, false); ens Failure(-1, r); Norm (res=r)
@*)
= handle xs



(* The following examples are adapted from Oleg Kiselyov
   "Non-deterministic choice amb"
   (c.f. https://okmij.org/ftp/ML/ML.html#amb) *)

(*


let m1 xs 
(*@ ex r ; Choose(emp, (xs), true); ens res = r /\ r=7 
 \/ ex r ; Choose(emp, (xs), false); Failure(emp, 500, r); Norm(res=r)
@*)
= if amb xs then perform (Failure 500) else 42 


let branch_example (): int
(*@ branch_example(res): req true; ens res=42 @*)
= handle m1 [(fun () -> true); (fun () -> true); (fun () -> true); (fun () -> false)]
*)

let _ =
  (*let v = branch_example () in
  Printf.printf "(%d)\n%!" v;*)
  let v = branch_example_generic [(fun () -> false); (fun () -> false); (fun () -> false); (fun () -> true)] in
  Printf.printf "(%d)\n%!" v;
   
   
   
*)