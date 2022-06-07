
open List
open Parsetree
open Pretty
(*open Z3

let rec term_to_expr ctx : Parsetree.term -> Expr.expr = function
  | Num n        -> Arithmetic.Integer.mk_numeral_i ctx n
  | Var v          -> Arithmetic.Integer.mk_const_s ctx v
  | Plus (t1, t2)  -> Arithmetic.mk_add ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]
  | Minus (t1, t2) -> Arithmetic.mk_sub ctx [ term_to_expr ctx t1; term_to_expr ctx t2 ]


let rec pi_to_expr ctx : Parsetree.pi -> Expr.expr = function
  | True                -> Boolean.mk_true ctx
  | False               -> Boolean.mk_false ctx
  | Atomic (op, t1, t2) -> (
      let t1 = term_to_expr ctx t1 in
      let t2 = term_to_expr ctx t2 in
      match op with
      | EQ -> Boolean.mk_eq ctx t1 t2
      | LT -> Arithmetic.mk_lt ctx t1 t2
      | LTEQ -> Arithmetic.mk_le ctx t1 t2
      | GT -> Arithmetic.mk_gt ctx t1 t2
      | GTEQ -> Arithmetic.mk_ge ctx t1 t2)
  | And (pi1, pi2)      -> Boolean.mk_and ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  | Or (pi1, pi2)       -> Boolean.mk_or ctx [ pi_to_expr ctx pi1; pi_to_expr ctx pi2 ]
  | Imply (pi1, pi2)    -> Boolean.mk_implies ctx (pi_to_expr ctx pi1) (pi_to_expr ctx pi2)
  | Not pi              -> Boolean.mk_not ctx (pi_to_expr ctx pi)


let check p1 p2 : bool =
  let pi =   (Not (Or (Not p1, p2))) in
  let cfg = [ ("model", "false"); ("proof", "false") ] in
  let ctx = mk_context cfg in
  let expr = pi_to_expr ctx pi in
  (* print_endline (Expr.to_string expr); *)

  let solver = Solver.mk_simple_solver ctx in
  Solver.add solver [ expr ];
  let sat = not (Solver.check solver [] == Solver.SATISFIABLE) in
  (*print_endline (Solver.to_string solver); *)
  sat

let check_pure p1 p2 : (bool * string) = 
  let sat = check  p1 p2 in
  let _ = string_of_pi p1 ^" => " ^ string_of_pi p2 in 
  let buffur = ("[PURE]"(*^(pure)*)^ " " ^(if sat then "Succeed\n" else "Fail\n")  )
  in (sat, buffur)

*)


let rec  nullable (es:es) : bool=
  match es with
    Emp -> true
  | Bot -> false 
  | Event _ -> false 
  | Cons (es1 , es2) -> ( nullable es1) && ( nullable es2)
  | ESOr (es1 , es2) -> ( nullable es1) || ( nullable es2)
  | Kleene _ -> true
  | Infiny _ -> true

  | Underline -> false 
  | Omega _ -> false
  | Not _ -> false
  | Emit _ -> false
  | Await _ -> false  

;;





let rec  fst (es:es): event list = 
  match es with
  | Bot -> []
  | Emp -> []
  | Event ev ->  [One (ev)]
  | Not (ev) ->  [Zero (ev)]
  | Cons (es1 , es2) ->  if  nullable es1 then append ( fst es1) ( fst es2) else  fst es1
  | ESOr (es1, es2) -> append ( fst es1) ( fst es2)
  | Kleene es1 ->  fst es1
  | Omega es1 ->  fst es1
  | Infiny es1 ->  fst es1

  | Underline -> [Any]
  | Emit (ins) -> [Send (ins)]
  | Await (ins) -> [Receive (ins)]

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

let isEmpSpec ((_, es, _):spec) : bool = 
  isEmp es;; 

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
      if entailsEvent ev (One ev1) then Emp else Bot
  | Emit ins -> 
      if entailsEvent ev (Send ins)  then Emp else Bot
  | Await ins -> 
      if entailsEvent ev (Receive ins)  then Emp else Bot
  
  | Not ev1 -> if entailsEvent ev (Zero ev1) then Emp else Bot  


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
  | Infiny es1 -> Cons  (derivative es1 ev, es)

  | Omega es1 -> Cons  (derivative es1 ev, es)
  | Underline -> Emp


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







(*(bool * binary_tree ) *)
let check_containment lhs rhs : (bool * string) = 
  let _ = (string_of_es (normalES lhs)) ^ " |- " ^ (string_of_es (normalES rhs)) (*and i = INC(lhs, rhs)*) in

  let (re, tree) =  containment [] lhs rhs in
  let result = printTree ~line_prefix:"* " ~get_name ~get_children tree in
  let buffur = ("[ENTAILMENT] " (*^ (entailment)*)^(if re then "Succeed\n" else "Fail\n")  ^ result)
  in (re , buffur)

let compareInstant (s1, i1) (s2, i2) : bool = 
  let rec helper l1 l2 : bool = 
    match (l1, l2) with 
    | ([], []) -> true 
    | (x::xs, y::ys)  -> x == y && helper xs ys
    | _ -> false 
  in 
  (String.compare s1 s2 == 0)  && helper i1 i2

let rec existSide (ins) (side:side) : (string * (es * es))  option = 
  match side with 
  | [] -> None
  | (ins1, (es1, es2)):: xs -> if String.equal ins ins1 then Some (ins1, (es1, es2)) else existSide ins xs 

let check_side (s1:side) (s2:side)  : (bool * string) = 
  let result = 
    List.fold_left (fun acc (ins2, (es21, es22)) -> acc && 
    (
      match existSide ins2 s1 with
      | None -> raise (Foo ("check_side: " ^ ins2 ^ string_of_side s1)) 
      | Some (_, (es11, es12)) -> (* es12 < es22, es21 < es11*)
        let (re1, _) = check_containment es21 es11  in 
        let (re2, _) = check_containment es12 es22  in 
        (*
        print_string ("side...\n" ^str1^"\n");
        print_string (str2^"\n");*)
        re1 && re2
    )
  ) true s2  in 
  let buffur = ("[SIDE]" ^ (* (string_of_bool result)^*)" " ^(if result then "Succeed\n" else "Fail\n")  )
  in (result, buffur)


let printReport ((_, lhs, side1):spec) ((_, rhs, side2):spec) :(bool * string) = 
  let startTimeStamp = Sys.time() in
  (*let (re1, _) = check_pure pi1 pi2 in *)
  let (re2, temp2) = check_containment lhs rhs in 
  let (re3, temp3) = check_side side1 side2  in 
  let verification_time = "[Verification Time: " ^ string_of_float ((Sys.time() -. startTimeStamp) *. 1000.0) ^ " ms]" in

  let re = re2 && re3 in 
  let whole = "[Verification Result: " ^ (if re  then "Succeed" else "Fail" ) in 
  (re, (*"===========================================\n" ^*)
  verification_time  ^"\n"^
  whole  ^"\n"^
  "------------------------------\n" ^
  (*
  temp1 ^ 
  "- - - - - - - - - - - - - -"^"\n" ^ *)
  temp3 ^ 
  "- - - - - - - - - - - - - -"^"\n" ^
  temp2)
  ;;

let n_GT_0 : pi =
  Atomic (LT, Var "n", Num 0)

let n_GT_1 : pi =
  Atomic (LT, Var "n", Num 5)


let testSleek (): string =
  let spec1 = (n_GT_0, Emp, [("Foo",(Emp,  Emp))]) in 
  let spec2 = (n_GT_1, Emp, [("Foo",(Emp,  Event ("A", [])))]) in 
  let (_, str) = printReport spec1 spec2 in str;;






