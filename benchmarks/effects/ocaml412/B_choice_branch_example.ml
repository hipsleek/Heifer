(* McCarthy's locally angelic choice operator (angelic modulo nontermination). *)

effect Choose : (unit -> bool) list -> bool
effect Success : int -> unit 
effect Failure : int -> int 

let amb (xs : (unit -> bool) list) : bool
(*@ ex r; Choose(emp, (xs), r) @*)
= perform (Choose xs)

(* ~predicate any_list(list) = 
   list=[]  \/ ex hd tl; any_list(tl) /\ list = hd::tl   @*)

let rec iter (f:((unit -> bool) -> unit))  (xs:(unit -> bool) list) :  unit
(*@ req xs=[]; Norm(res=())
    ex h t r1 r2; req xs=h::t; f(h, r1); iter(f, t, r2); Norm(res=())  @*)
= match xs with
  | [] -> ()
  | h::t -> f h; iter f t


let handle (m:((unit -> bool) list -> int)) (xs:(unit -> bool) list) : int 
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
    perform (Failure (-1))
  with 
  | effect (Success r) k -> r
  | x -> x  

(*@
containRetTrue (xs) = 
  ex r; req xs =[] ; Norm(res=r /\ r=false)
\/ex h t; req xs = t::l; h(emp, (), true);  Norm(res=r /\ r=true)
\/ex h t; req xs = t::l; h(emp, (), false);  containRetTrue (t, r) ; Norm(res=r)
@*)

let m xs 
(*@ ex r ; Choose(emp, (xs), true); ens res = r /\ r=7 
 \/ ex r ; Choose(emp, (xs), false); Failure(emp, (-2), r); Norm(res=r)
@*)
= if amb xs then 7 else perform (Failure (-2))


let branch_example_generic (xs: (unit -> bool) list) : int
(*@ ex r; req containRetTrue (xs, true); ens res = r /\ r=7 
    ex r; req containRetTrue (xs, false); ens Failure(-1, r); Norm (res=r)
@*)
= handle m xs


let m1 xs 
(*@ ex r ; Choose(emp, (xs), true); ens res = r /\ r=7 
 \/ ex r ; Choose(emp, (xs), false); Failure(emp, (-2), r); Norm(res=r)
@*)
= if amb xs then perform (Failure (-2)) else 42 


(* The following examples are adapted from Oleg Kiselyov
   "Non-deterministic choice amb"
   (c.f. https://okmij.org/ftp/ML/ML.html#amb) *)

(* An angelic choice *always* picks the successful branch. *)
let branch_example (): int
(*@ branch_example(res): req true; ens res=42 @*)
= handle m1 [(fun () -> true); (fun () -> true); (fun () -> true); (fun () -> false)]

(* isContainFalse(xs, res) = 
  req xs=[]; ens res=false 
  req xs=h::t; h((), r); req r=false; ens res = true 
                      \/ req r=true; isContainFalse(t, res)
*)
let _ =
  let v = branch_example () in
  Printf.printf "(%d)\n%!" v;
  let v = branch_example_generic [(fun () -> false); (fun () -> false); (fun () -> false); (fun () -> true)] in
  Printf.printf "(%d)\n%!" v;
   
