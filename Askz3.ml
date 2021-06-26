
open Ast
open List
open Sys
open Unix
open Printf

exception FooAskz3 of string

let rec convertTerm (t:terms):string = 
  match t with
    Var name -> " " ^ name ^ " "
  | Number n -> " " ^ string_of_int n ^ " "
  | Plus (t1, t2) -> ("(+") ^ (convertTerm t1) ^  (convertTerm t2) ^ ")"
  | Minus (t1, t2) -> ("(-") ^ (convertTerm t1) ^  (convertTerm t2) ^ ")"
  ;;

let rec convertPure (pi:pure) (acc:string):string = 
  match pi with
    TRUE -> "(< 0 1)"
  | FALSE -> "(> 0 1)"
  | Gt (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(>" ^ temp1 ^ temp2 ^")"
  | Lt (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(<" ^ temp1 ^ temp2 ^")"
  | GtEq (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(>=" ^ temp1 ^ temp2 ^")"
  | LtEq (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(<=" ^ temp1 ^ temp2 ^")"
  | Eq (t1, t2) -> 
      let temp1 = convertTerm t1 in
      let temp2 = convertTerm t2 in
      acc ^ "(=" ^ temp1 ^ temp2 ^")"
  | PureAnd (pi1,pi2) -> 
      let temp1 = convertPure pi1 "" in
      let temp2 = convertPure pi2 "" in
      acc ^ "(and" ^temp1 ^ temp2 ^ ")"
  | Neg piN -> 
      let temp1 = convertPure piN "" in
      acc ^ "(not" ^temp1 ^ ")"
  | PureOr (pi1,pi2) -> 
      let temp1 = convertPure pi1 "" in
      let temp2 = convertPure pi2 "" in
      acc ^ "(or" ^temp1 ^ temp2 ^ ")"
      ;;

let rec exist li ele = 
  match li with 
    [] -> false 
  | x :: xs -> if (String.compare x ele) == 0 then true else exist xs ele
  ;;

let rec checkRedundant (li:string list) : string list = 
  match li with
    [] -> []
  | x ::xs -> if (exist xs x) == true then checkRedundant xs else append [x] (checkRedundant xs)

;;


let rec getAllVarFromTerm (t:terms) (acc:string list):string list = 
  match t with
  Var name -> append acc [name]
| Plus (t1, t2) -> 
    let cur = getAllVarFromTerm t1 acc in 
    getAllVarFromTerm t2 cur
| Minus (t1, t2) -> 
    let cur = getAllVarFromTerm t1 acc in 
    getAllVarFromTerm t2 cur
| _ -> acc
;;

let rec getAllVarFromPure (pi:pure) (acc:string list):string list = 
  match pi with
    TRUE -> acc
  | FALSE -> acc
  | Gt (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      append acc (append allVarFromTerm1 allVarFromTerm2)
  | Lt (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      append acc (append allVarFromTerm1 allVarFromTerm2)
  | GtEq (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      append acc (append allVarFromTerm1 allVarFromTerm2)
  | LtEq (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      append acc (append allVarFromTerm1 allVarFromTerm2)
  | Eq (term1, term2) -> 
      let allVarFromTerm1 = getAllVarFromTerm term1 [] in
      let allVarFromTerm2 = getAllVarFromTerm term2 [] in
      append acc (append allVarFromTerm1 allVarFromTerm2)
  | PureAnd (pi1,pi2) -> 
      let temp1 = getAllVarFromPure pi1 [] in
      let temp2 = getAllVarFromPure pi2 [] in
      append acc (append temp1 temp2) 
  | Neg piN -> 
      append acc (getAllVarFromPure piN [])
  | PureOr (pi1,pi2) -> 
      let temp1 = getAllVarFromPure pi1 [] in
      let temp2 = getAllVarFromPure pi2 [] in
      append acc (append temp1 temp2) 
  ;;


let addAssert (str:string) :string =
  "(assert " ^ str ^ " ) \n (check-sat) \n"
  ;;


let askZ3 pi = 
  (*
  let startTimeStamp = Sys.time() in
  *)
  
  let inFile = Sys.getcwd () ^ "/askZ3.txt" in
  let outFile = Sys.getcwd () ^ "/answerZ3.txt" in 
  let declear = List.fold_right (fun v acc ->acc ^ ("(declare-const " ^ v ^ " Int)\n") ) (checkRedundant (getAllVarFromPure pi [])) "" in
  let assertions = addAssert (convertPure (pi) "") in
  let oc = open_out inFile in    (* 新建或修改文件,返回通道 *)
      (*print_string (declear^assertions^"\n************\n");   (* 写一些东西 *)
*)
      fprintf oc "%s\n" (declear^assertions);   (* 写一些东西 *)
      close_out oc;                (* 写入并关闭通道 *)
      ignore (Sys.command ("z3 -smt2 "^ inFile ^" > " ^ outFile));
      let ic = open_in outFile in
      try 
        let line = input_line ic in  (* 从输入通道读入一行并丢弃'\n'字符 *)
        close_in ic ;                 (* 关闭输入通道 *) 
        (*
        let verification_time = "[askZ3 Time: " ^ string_of_float (Sys.time() -. startTimeStamp) ^ " s]\n" in

        print_string (verification_time); 
        *)
        match line with 
        "sat" -> true
        | "unsat" -> false 
        | _ -> false 
      with e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)
      
;;
                


(*

let rec getTermNameFromTerm (t:terms) =
  match t with 
    Var name -> name
  | Plus (ter, num) -> getTermNameFromTerm ter
  | Minus (ter, num) -> getTermNameFromTerm ter
  ;;

let rec getZ3ExprFromTerm (term:terms) ctx = 
  match term with
    Var name -> 
      let name_is = (Symbol.mk_string ctx name) in
      let x_is = Integer.mk_const ctx name_is in
      x_is
  | Plus (t, num) -> 
      let name_is = (Symbol.mk_string ctx (getTermNameFromTerm t))  in
      let x_is = Integer.mk_const ctx name_is in
      let make_plus = Arithmetic.mk_add ctx [ x_is ; (Integer.mk_numeral_i ctx num)] in
      make_plus
  | Minus (t, num) -> 
      let name_is = (Symbol.mk_string ctx (getTermNameFromTerm t))  in
      let x_is = Integer.mk_const ctx name_is in
      let make_minus = Arithmetic.mk_add ctx [ x_is ; (Integer.mk_numeral_i ctx (0 - num))] in
      make_minus
  ;;

let rec getZ3ConstrainFromPure pi ctx acc= 
  match pi with 
    TRUE -> acc 
  | FALSE -> 
      let name_is = (Symbol.mk_string ctx "constructFalse") in
      let x_is = Integer.mk_const ctx name_is in
      let x1 = (mk_gt ctx (x_is) 
          (Integer.mk_numeral_i ctx 0)) in
      let x2 = (mk_eq ctx (x_is) 
          (Integer.mk_numeral_i ctx 0)) in
      append acc [x1;x2]
  | Gt (term, num) -> 
      let expr = getZ3ExprFromTerm term ctx in 
      let assertion = mk_gt ctx expr (Integer.mk_numeral_i ctx num) in
      append acc [assertion]
  | Lt (term, num) -> 
      let expr = getZ3ExprFromTerm term ctx in 
      let assertion = (mk_lt ctx expr (Integer.mk_numeral_i ctx num)) in
      append acc [assertion]
  | Eq (term, num) -> 
      let expr = getZ3ExprFromTerm term ctx in 
      let assertion = (mk_eq ctx expr (Integer.mk_numeral_i ctx num)) in
      append acc [assertion]
  | PureAnd (pi1,pi2) -> 
      let assert1 = getZ3ConstrainFromPure pi1 ctx [] in
      let assert2 = getZ3ConstrainFromPure pi2 ctx [] in
      append (append acc assert1) assert2
  | Neg piN -> 
      let assert1 = getZ3ConstrainFromPure piN ctx [] in
      let makenot = mk_not ctx (List.nth assert1 0)  in
      append acc [makenot]
  | PureOr (pi1,pi2) -> 
      let assert1 = getZ3ConstrainFromPure pi1 ctx [] in
      let assert2 = getZ3ConstrainFromPure pi2 ctx [] in
      let makeOr = Boolean.mk_or ctx (append assert1 assert2) in
      append acc [makeOr]

;;
let askZ3 pi = 
  let z3_context = Z3.mk_context [] in
  let constrains = getZ3ConstrainFromPure pi z3_context [] in
  let solver = Z3.Solver.mk_solver z3_context None in
  let () = Z3.Solver.add solver constrains in
    match Z3.Solver.check solver [] with
    | UNSATISFIABLE -> 
      (*Printf.printf "unsat\n" *)
      false
    | UNKNOWN -> 
      (*Printf.printf "unknown"*)
      false
    | SATISFIABLE -> true
        (*match Z3.Solver.get_model solver with
        | None -> ()
        | Some model ->
            Printf.printf "%s\n"
                (Z3.Model.to_string model)*)


Sys.command ("z3 askZ31.txt > z3Answer.1txt");;*)




  
    
(*
let a  = FALSE ;;
let b = TRUE;;
let c = Gt (Var "h",10);;
let d = Lt (Var "s",0);;
let f = Eq (Minus (Var "h",1),0);;
let g p1 p2 = PureAnd (p1,p2);;
let o p1 p2 = PureOr (p1,p2);;
let p p1 = Neg p1;;




print_endline (addAssert (convertPure (g (o b c) (g c f)) ""));;
print_endline (addAssert (convertPure (b) ""));;
print_endline (addAssert (convertPure (c) ""));;
print_endline (addAssert (convertPure (d) ""));;
print_endline (addAssert (convertPure (g b c) ""));;
print_endline (addAssert (convertPure (o b c) ""));;
print_endline (addAssert (convertPure (p c) ""));;
*)
