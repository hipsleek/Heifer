effect IsALeaf : unit
effect IsANode : int -> unit 

type tree =
  | Leaf
  | Node of int * tree * tree

(* the code below constructs this tree:
         4
       /   \
      2     5
     / \   / \
    1   3 6   7
*)
let t =
  Node(4,
    Node(2,
      Node(1, Leaf, Leaf),
      Node(3, Leaf, Leaf)
    ),
    Node(5,
      Node(6, Leaf, Leaf),
      Node(7, Leaf, Leaf)
    )
  )

(* recursion outside the handler *)
let rec size = function
  | Leaf -> 0
  | Node (_, l, r) -> 1 + size l + size r

let rec test (i:int ref) n 
(* ensures (n=0, emp) \/ (n!=0, {i->i+1}^* ) *)
= 
  if n == 0 then ()
  else i := !i + 1; test i (n-1)

(* recursion within the handler *)
let rec travasetree t = 
  match t with 
  | Leaf -> perform IsALeaf 
  | Node (c, l, r) -> perform (IsANode c); travasetree l; travasetree r


let main = (*print_string (string_of_int (size t)^"\n")*)
  let i = Sys.opaque_identity (ref 0) in
  let () = match travasetree t with 
  | v -> v 
  | effect IsALeaf k -> continue k ()
  | effect (IsANode c) k -> i := !i + 1; print_string (string_of_int c ^ "\n"); continue k ()
  in print_string ("\n"^strihan1o n g s hng_of_int (!i)^"\n")

