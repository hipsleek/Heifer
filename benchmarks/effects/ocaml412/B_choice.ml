(**
  * McCarthy's locally angelic choice
  *)

effect Choose : (unit -> 'a) list -> 'a

let amb : (unit -> 'a) list -> 'a
  = fun xs -> perform (Choose xs)

let first_success (type b) : ('a, b) continuation -> (unit -> 'a) list -> b
  = fun f gs ->
  let exception Success of b in
  let last = List.length gs - 1 in
  try
    List.iteri
      (fun i g ->
        try
          let x = g () in
          let f = if i = last then f else Obj.clone_continuation f in
          raise (Success (continue f x))
          (* 这里之后Success 的情况才能到达 *)
        with 
        | (Success _) as e -> raise e
        | _ -> ())
      gs; raise (Failure "no success")
  with Success r -> r

let handle : (unit -> 'a) -> 'a
  = fun m ->
  (* McCarthy's locally angelic choice operator (angelic modulo
     nontermination). *)
    match m () with
    | v -> v
    | exception e -> raise e
    | effect (Choose xs) k -> first_success k xs

(* The following examples are adapted from Oleg Kiselyov
   "Non-deterministic choice amb"
   (c.f. https://okmij.org/ftp/ML/ML.html#amb) *)

(* More involved example, requiring `amb` to make three correct
   choices. *)


(*@  existsPyth(xs, res): 
  ex i, j, k;     req isContain xs i /\ isContain xs j /\ isContain xs k /\ i*i + j*j = k*k; ens res=true 
  forall i, j, k; req isContain xs i /\ isContain xs j /\ isContain xs k /\ i*i + j*j!= k*k; ens res=false 
@*)


let pyth : int list -> bool (*int * int * int*)
(*@ pyth(xs, res): 
    req existsPyth(xs, true); ens res = true
    req existsPyth(xs, false); ens Failure("no success") @*)
  = fun numbers -> 
  let numbers' = List.map (fun n -> (fun () -> n)) numbers in
  handle (fun () ->
      let i = amb numbers' in
      let j = amb numbers' in
      let k = amb numbers' in
      if i*i + j*j = k*k
      then 
        (print_endline (string_of_int i ^ " " ^ string_of_int j ^ " "^ string_of_int k);
        true)
      else failwith "no solution")

let pyth_example () = pyth [20;21;29;1;2;3;4;5;]

let _ =
  let b = pyth_example () in
  Printf.printf "(%b)\n%!" b
