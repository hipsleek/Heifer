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

let rec delete_aux m (i:int) : ((int * bool) list) = 
  match m with 
  | [] -> [] 
  | (idx, assign) :: xs -> 
    if i == idx 
    then xs 
    else (idx, assign) :: (delete_aux xs i)

let rec delete (idx:int) = 
  my_record := delete_aux !my_record idx

let rec insert (i, b)  = 
  my_record := (i, b) ::!my_record

let rec string_of_record (m:((int * bool) list)) : string = 
  match m with 
  | [] -> ""
  | (idx, assign) :: xs -> 
    string_of_int idx ^ " : " ^ 
    string_of_bool assign ^ "\n" ^ 
    string_of_record xs 

let satisfy (p:oprations): bool = 
  match (interp p) with 
  | v -> v 
  | effect (Lable idx) k -> 
    print_string ("\n------------ \n");
    print_string(string_of_record (!my_record));
    (
      match lookup !my_record idx with
      | Some b -> continue k b 
      | None -> 
        (insert (idx, true); (continue (Obj.clone_continuation k) true)) 
        || 
        (delete idx; insert (idx, false); 
          ((continue k false) 
          || 
          (delete idx; false))
        )
    )

let test = Or (And (Lit (true, 0), Lit (false, 0)), And (Lit (true, 1), Lit (false, 0)))

let main = 
  let res = satisfy test in 
  print_string (string_of_bool res ^ "\n")