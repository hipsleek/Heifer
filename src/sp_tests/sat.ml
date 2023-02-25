effect Lable : int -> bool 

type oprations = 
  | And of (oprations * oprations) 
  | Or of (oprations * oprations)
  | Lit of (bool * int) 

let rec interp (p:oprations): bool = 
  match p with 
  | And (p1, p2) ->  interp p1 && interp p2
  | Or (p1, p2) ->  interp p1 || interp p2
  | Lit (b, i) ->  if b then perform (Lable i) else not (perform (Lable i))

let (my_record : ((int * bool) list) ref) = ref [] 

let rec lookup m (i:int) : bool option = 
  match m with 
  | [] -> None 
  | (idx, assign) :: xs -> 
    if i == idx 
    then Some assign 
    else lookup xs i

let rec delete m (i:int) : ((int * bool) list) = 
  match m with 
  | [] -> [] 
  | (idx, assign) :: xs -> 
    if i == idx 
    then xs 
    else (idx, assign) :: (delete xs i)

let satisfy (p:oprations): bool = 
  match (interp p) with 
  | v -> v 
  | effect (Lable idx) k -> 
    (
      match lookup !my_record idx with
      | Some b -> continue k b 
      | None -> 
        (my_record := (idx, true)::!my_record; (continue (Obj.clone_continuation k) true)) 
        || 
        (my_record := (idx, false)::!my_record; 
          ((continue k false) 
          || 
          (my_record := delete !my_record idx; false)
          )
        )
    )

let test = Or (And (Lit (true, 0), Lit (false, 0)), And (Lit (true, 1), Lit (false, 0)))

let main = 
  let res = satisfy test in 
  print_string (string_of_bool res ^ "\n")