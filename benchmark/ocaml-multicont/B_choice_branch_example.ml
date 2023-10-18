(**
  * McCarthy's locally angelic choice
  *)

open Effect.Deep

type _ Effect.t += Choose : (unit -> bool) list -> bool Effect.t

let amb : (unit -> bool) list -> bool
  = fun xs -> Effect.perform (Choose xs)

let handle : (unit -> int) -> int
  = fun m ->
  (* McCarthy's locally angelic choice operator (angelic modulo
     nontermination). *)
  let hamb =
    { retc = (fun x -> 
      print_endline ("retc: " ^ string_of_int x);
      x)
    ; exnc = (fun e -> 
      print_endline ("exnc: " ^  Printexc.to_string e);
      raise e)
    ; effc = (fun (type b) (eff : b Effect.t) ->
      match eff with
      | Choose xs ->
         Some
           (fun (k : (b, _) continuation) ->
             let open Multicont.Deep in
             let r = promote k in

(* first_success: Iteration to find the fist success case *)
  let exception Success of int in
  try
    List.iter
      (fun g ->
        try
          let (x:bool) = g () in
          print_endline ("first_success: " ^ string_of_bool x);
          let temp = (resume r) x in 
          print_endline ("Success: " ^ string_of_int temp);
          raise (Success (temp))
        with 
        | (Success _) as e -> raise e
        | _ -> print_endline ("_"); ())
      xs; 
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
  = fun () ->
  handle (fun () ->
      if amb [(fun () -> true); (fun () -> true); (fun () -> false); (fun () -> false)]
      then failwith "Fail"
      else 42)

let _ =
  let v = branch_example () in
  Printf.printf "(%d)\n%!" v
