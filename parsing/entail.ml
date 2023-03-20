
(* basic term *)
type basic_t = BINT of int | UNIT | VARName of string | List of int list 

(* an occurrence of an effect *)
type instant = Instant of string * basic_t list

type term = 
    | Num of int
    | TList of (term list)
    | TTupple of (term list)
    | Var of string
    | Plus of term * term 
    | Minus of term * term 
    | TListAppend of term * term

type bin_op = GT | LT | EQ | GTEQ | LTEQ

type pi = 
  | True
  | False
  | Atomic of bin_op * term * term
  | And    of pi * pi
  | Or     of pi * pi
  | Imply  of pi * pi
  | Not    of pi 
  | Predicate of string * term

type kappa = 
  | EmptyHeap
  | PointsTo of (string * term)
  | SepConj of kappa * kappa

type stagedSpec = 
      (* common *)
      | Exists of (string list)
      | Require of kappa 
      (* higher-order functions *)
      | Ensures of kappa 
      | HigherOrder of (string * basic_t list)
      (* effects *)
      | NormalReturn of (kappa * basic_t list)
      | RaisingEff of (kappa * instant * basic_t ) (* basic_t is a placeholder for the resumned value *)

(* type linearStagedSpec = stagedSpec list *)

(* type spec = (pi * linearStagedSpec) list  *)
type spec = stagedSpec list 

let string_of_basic_type a : string = 
  match a with 
  | BINT i -> string_of_int i 
  | UNIT -> "()"
  | VARName s -> s
  | List s ->
    Format.asprintf "[%s]"
      (List.map string_of_int s |> String.concat "; ")


let string_of_args args =
  List.map string_of_basic_type args |> String.concat ", "

let rec string_of_term t : string = 
  match t with 
  | Num i -> string_of_int i 
  | Var str -> str
  | Plus (t1, t2) -> string_of_term t1 ^ " + " ^ string_of_term t2
  | Minus (t1, t2) -> string_of_term t1 ^ " - " ^ string_of_term t2
  | TTupple nLi -> 
    let rec helper li = 
      match li with
      | [] -> ""
      | [x] -> string_of_term x
      | x:: xs -> string_of_term x ^","^ helper xs 
    in "(" ^ helper nLi ^ ")"

  | TList nLi -> 
    let rec helper li = 
      match li with
      | [] -> ""
      | [x] -> string_of_term x
      | x:: xs -> string_of_term x ^";"^ helper xs 
    in "[" ^ helper nLi ^ "]"
  | TListAppend (t1, t2) -> string_of_term t1 ^ " ++ " ^ string_of_term t2

let rec string_of_kappa (k:kappa) : string = 
  match k with
  | EmptyHeap -> "emp"
  | PointsTo  (str, args) -> Format.sprintf "%s->%s" str (List.map string_of_term [args] |> String.concat ", ")
  | SepConj (k1, k2) -> string_of_kappa k1 ^ "*" ^ string_of_kappa k2 
  (* | Implication (k1, k2) -> string_of_kappa k1 ^ "-*" ^ string_of_kappa k2  *)

let string_of_stages (st:stagedSpec) : string =
  match st with
  | Require h ->
    Format.asprintf "req %s" (string_of_kappa h)
  | Ensures h ->
    Format.asprintf "%s" (string_of_kappa h)
  | HigherOrder (f, args) ->
    Format.asprintf "%s$(%s)" f (string_of_args args)
  | NormalReturn (heap, args) ->
    Format.asprintf "Norm(%s, %s)" (string_of_kappa heap) (string_of_args args)
  | RaisingEff (heap, Instant (name, args), ret) ->
    Format.asprintf "%s(%s, %s, %s)" name (string_of_kappa heap) (string_of_args args) (string_of_basic_type ret)
  | Exists vs ->
    Format.asprintf "ex %s" (String.concat " " vs)

let string_of_spec (spec:spec) :string =
  spec |> List.map string_of_stages |> String.concat "; "

let string_of_option to_s o :string =
  match o with
  | Some a -> "Some " ^ to_s a
  | None -> "None"

(* 
Flatten Form
============
S ::= req H | H & Norm | H & Eff | local v*
N ::= \/ {S;..;S}
*)

let check_entail : spec -> spec -> spec option =
  fun n1 _n2 ->
    Some n1

let%expect_test "entailments" =
  let test l r = Format.printf "%s |- %s ==> %s@." (string_of_spec l) (string_of_spec r) (check_entail l r |> string_of_option string_of_spec) in
  test [Ensures (PointsTo ("x", Num 1))] [Ensures (PointsTo ("x", Num 1))];
  [%expect {| [1; 2; 3] |}]