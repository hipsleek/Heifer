(* 
EXAMPLE 1: 
“Alice” ++ ⟨“ has ” ++ (Sk.(k “a dog”) ++ “ and the dog”++ (k “a bone.”))⟩
*)

effect Has : string
effect Alice : string

let delimited_has () =
  " has " ^ (perform Has)

let helper () = 
  match  delimited_has ()  with 
  | x -> x 
  | effect Has k -> 
  (continue k "a dog") ^ " and the dog" ^ (continue (Obj.clone_continuation k) "a bone.")

let example1 = 
  "Alice" ^ helper ()

(*
EXAMPLE 2: 
⟨“Alice” ++ ⟨“ has ” ++ (Sk1.Sk2.“A cat” ++ (k1 (k2 “.”)))⟩⟩
*)
let delimited_Alice () =
  "Alice" ^ (perform Alice)

let example2 = 
  match delimited_Alice () with 
  | x -> x 
  | effect Alice k2 -> 
    (match delimited_has () with 
    | x -> x 
    | effect Has k1 -> "A cat" ^ (continue k1 (continue k2 "."))
    )

let main = 
  print_string (example1 ^ "\n");
(* Alice has a dog and the dog has a bone. *)
  print_string (example2 ^ "\n")
(* A cat has Alice. *)

