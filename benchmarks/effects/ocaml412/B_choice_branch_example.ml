
effect Choose : (unit -> bool) list -> bool
effect Success : int -> unit 
effect Failure : string -> int 

let amb xs : bool
= perform (Choose xs)


let rec iter (f:(bool -> 'a -> unit))  (xs:'a list):  unit
(* iter(f, xs, unit):
  req xs=[]; ens res=unit
  req xs=h::t; f$(h, _); iter$(f, t, unit); ens res=()  *)
= match xs with
  | [] -> ()
  | [h] -> f true h
  | h::t -> f false h; iter f t

let handle : (unit -> int) -> int
  = fun m ->
  (* McCarthy's locally angelic choice operator (angelic modulo
     nontermination). *)
  match m () with
  | x -> x
  | exception e -> raise e
  | effect (Choose xs) k ->

(* first_success: Iteration to find the fist success case *)
  match 
    iter
      (fun last g ->
        match
          let (x:bool) = g () in
          let k = if last then k else Obj.clone_continuation k in
          let temp = continue k x in
          perform (Success (temp))
        with
        | effect (Success x) k -> perform (Success (x))
        | effect (Failure x) k -> ()
        | exception e -> ()
        | _ -> ()
      ) xs;
    perform (Failure "no success")
  with 
  | effect (Success r) k -> r
  | x -> x  

(* end  to find the fist success case *)
(* first_success (resume r) xs*)


(* The following examples are adapted from Oleg Kiselyov
   "Non-deterministic choice amb"
   (c.f. https://okmij.org/ftp/ML/ML.html#amb) *)

(* An angelic choice *always* picks the successful branch. *)
let branch_example : unit -> int
(*@ branch_example(res): req true; ens res=42 @*)
  = fun () ->
  handle (fun () ->
      if amb [(fun () -> true); (fun () -> true); (fun () -> true); (fun () -> false)]
      then perform (Failure "Fail")
      else 42)

(* isContainFalse(xs, res) = 
  req xs=[]; ens res=false 
  req xs=h::t; h((), r); req r=false; ens res = true 
                      \/ req r=true; isContainFalse(t, res)
*)

let branch_example_generic : (unit -> bool) list -> int
(*@ branch_example_generic(xs, res): 
    req isContainFalse xs; ens res = 7 
    req !isContainFalse xs; ens Failure("no success")
@*)
  = fun xs ->
  handle (fun () ->
      if amb xs
      then perform (Failure "Fail")
      else 7)

let _ =
  let v = branch_example () in
  Printf.printf "(%d)\n%!" v;
  let v = branch_example_generic [(fun () -> true); (fun () -> true); (fun () -> true); (fun () -> false)] in
  Printf.printf "(%d)\n%!" v;
