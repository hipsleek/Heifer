(**
  * McCarthy's locally angelic choice
  *)

open Effect.Deep
open Multicont.Deep 

type _ Effect.t += Choose : (unit -> bool) list -> bool Effect.t
exception Success of int

let amb : (unit -> bool) list -> bool
(* amb(xs, res) : Choose(xs, res) *)
  = fun xs -> Effect.perform (Choose xs)

let rec iter (f:('a -> unit))  (xs:'a list):  unit 
(* iter(f, xs, unit):  
  req xs=[]; ens res=unit 
  req xs=h::t; f$(h, _); iter$(f, t, unit); ens res=()  *)
= match xs with 
  | [] -> () 
  | h::t -> f h; iter f t 

let handle : (unit -> int) -> int
  = fun m ->
  (* McCarthy's locally angelic choice operator (angelic modulo
     nontermination). *)
  let hamb =
    { retc = (fun x -> x)
    ; exnc = (fun e -> raise e)  (* print_endline ("exnc: " ^  Printexc.to_string e); *)
    ; effc = (fun (type b) (eff : b Effect.t) ->
      match eff with
      | Choose xs ->
         Some
           (fun (k : (b, _) continuation) ->
             let r = promote k in

(* first_success: Iteration to find the fist success case *)
  try
    iter
      (fun g ->
        try
          let (x:bool) = g () in
          let temp = (resume r) x in 
          raise (Success (temp))
        with 
        | (Success _) as e -> raise e
        | _ -> ()
      ) xs; 
    raise (Failure "no success")
  with Success r -> r
(* end  to find the fist success case *)
(* first_success (resume r) xs*)
            
            )
      | _ -> None) }
  in
  match_with m () hamb

(* The following examples are adapted from Oleg Kiselyov
   "Non-deterministic choice amb"
   (c.f. https://okmij.org/ftp/ML/ML.html#amb) *)

(* An angelic choice *always* picks the successful branch. *)
let branch_example : unit -> int
(*@ branch_example(res): req true; ens res=42 @*)
  = fun () ->
  handle (fun () ->
      if amb [(fun () -> true); (fun () -> true); (fun () -> false); (fun () -> false)]
      then raise (Failure "Fail")
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
      then raise (Failure "Fail")
      else 7)

let _ =
  let v = branch_example () in
  Printf.printf "(%d)\n%!" v;
  let v = branch_example_generic [(fun () -> true); (fun () -> true); (fun () -> false); (fun () -> false)] in
  Printf.printf "(%d)\n%!" v;

