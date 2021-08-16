
open List
open Parsetree
open Pretty





let rec  nullable (es:es) : bool=
  match es with
    Emp -> true
  | Bot -> false 
  | Event _ -> false 
  | Cons (es1 , es2) -> ( nullable es1) && ( nullable es2)
  | ESOr (es1 , es2) -> ( nullable es1) || ( nullable es2)
  | Kleene _ -> true
  | Underline -> false 
  | Omega _ -> false
  | Not _ -> false
  | Predicate _ -> raise (Foo ("nullable Predicate")) 

;;





let rec  fst (es:es): event list = 
  match es with
  | Bot -> []
  | Emp -> []
  | Event (ev) ->  [One (ev)]
  | Not (ev) ->  [Zero (ev)]
  | Cons (es1 , es2) ->  if  nullable es1 then append ( fst es1) ( fst es2) else  fst es1
  | ESOr (es1, es2) -> append ( fst es1) ( fst es2)
  | Kleene es1 ->  fst es1
  | Omega es1 ->  fst es1
  | Underline -> [Any]
  | Predicate _ -> raise (Foo ("fst Predicate")) 

;;

let rec esTail (es:es): event list = 
  match es with
  | Bot -> []
  | Emp -> []
  | Event (ev) ->  [One (ev)]
  | Not (ev) ->  [Zero (ev)]
  | ESOr (es1, es2) -> append ( esTail es1) ( esTail es2)
  | Kleene es1 ->  esTail es1
  | Omega es1 ->  esTail es1
  | Underline -> [Any]
  | Cons (es1 , es2) ->  if  nullable es2 then append ( esTail es1) ( esTail es2) else  esTail es2
  | Predicate _ -> raise (Foo ("esTail Predicate")) 

;;


let isBot (es:es) :bool= 
  match normalES es with
    Bot -> true
  | _ -> false 
  ;;

let isEmp (es:es) :bool= 
  match normalES es with
    Emp -> true
  | _ -> false 
  ;;

let rec checkexist lst super: bool = 
  match lst with
  | [] -> true
  | x::rest  -> if List.mem x super then checkexist rest super
  else false 
  ;;

let rec splitCons (es:es) : es list = 

  match es with 
    ESOr (es1, es2) -> append (splitCons es1) (splitCons es2)
  | _ -> [es]

  ;;


let rec reoccur esL esR (del:evn) = 
  match del with 
  | [] -> false 
  | (es1, es2) :: rest -> 
    let tempHL = splitCons es1 in 
    let tempL = splitCons esL in 

    let subsetL = checkexist tempL tempHL in 
      (*List.fold_left (fun acc a -> acc && List.mem a tempHL  ) true tempL in*)
    
    let tempHR = splitCons es2 in 
    let tempR = splitCons esR in 

    let supersetR = checkexist tempHR tempR in 
      (*List.fold_left (fun acc a -> acc && List.mem a tempR  ) true tempHR in*)
    
    if (subsetL && supersetR) then true
    else reoccur esL esR rest (*REOCCUR*) 
  ;;


let rec derivative (es:es) (ev:event): es =
  match es with
    Emp -> Bot
  | Bot -> Bot
  | Event ev1 -> 
      if compareEvent (One ev1) ev then Emp else Bot
  | Not ev1 ->       
      if compareEvent (Zero ev1) ev then Emp else Bot


  | ESOr (es1 , es2) -> ESOr (derivative es1 ev, derivative es2 ev)
  | Cons (es1 , es2) -> 
      if nullable es1 
      then let efF = derivative es1 ev in 
          let effL = Cons (efF, es2) in 
          let effR = derivative es2 ev in 
          ESOr (effL, effR)
      else let efF = derivative es1 ev in 
          Cons (efF, es2)    
  | Kleene es1 -> Cons  (derivative es1 ev, es)
  | Omega es1 -> Cons  (derivative es1 ev, es)
  | Underline -> Emp
  | Predicate _ -> raise (Foo ("derivative Predicate")) 


;;



let rec containment (evn: evn) (lhs:es) (rhs:es) : (bool * binary_tree ) = 
  let lhs = normalES lhs in 
  let rhs = normalES rhs in 
  let entail = string_of_inclusion lhs rhs in 
  if nullable lhs == true && nullable rhs==false then (false, Node (entail^ "   [DISPROVE]", []))
  else if isBot lhs then (true, Node (entail^ "   [Bot-LHS]", []))
  else if isBot rhs then (false, Node (entail^ "   [Bot-RHS]", []))
  else if reoccur lhs rhs evn then (true, Node (entail^ "   [Reoccur]", []))
  else 
  (*match lhs with 
    Disj (lhs1, lhs2) -> 
      let (re1, tree1) = containment evn lhs1 rhs in 
      let (re2, tree2) = containment evn lhs2 rhs in 
      (re1 && re2, Node (entail^ "   [LHS-DISJ]", [tree1; tree2]))
  | _ -> *)
    let (fst:event list) = fst lhs in 
    let newEvn = append [(lhs, rhs)] evn in 
    let rec helper (acc:binary_tree list) (fst_list:event list): (bool * binary_tree list) = 
      (match fst_list with 
        [] -> (true , acc) 
      | a::xs -> 
        let (result, (tree:binary_tree)) =  containment newEvn (derivative lhs a ) (derivative rhs a ) in 
        if result == false then (false, (tree:: acc))
        else helper (tree:: acc) xs 
      )
    in 
    let (result, trees) =  helper [] fst in 
    (result, Node (entail^ "   [UNFOLD]", trees))  
    
  ;;






let check_containment lhs rhs : (bool * binary_tree ) = 
  containment [] lhs rhs
  ;;

let printReport (lhs:es) (rhs:es) :string =


  let entailment = (string_of_es (normalES lhs)) ^ " |- " ^ (string_of_es (normalES rhs)) (*and i = INC(lhs, rhs)*) in

  let startTimeStamp = Sys.time() in
  let (re, tree) =  check_containment lhs rhs in
  let verification_time = "[Verification Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]\n" in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let buffur = ( "----------------------------------------"^"\n" ^(entailment)^"\n[Result] " ^(if re then "Succeed\n" else "Fail\n")  ^verification_time^" \n\n"^ result)
  in buffur
  
  ;;



