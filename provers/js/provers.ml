open Hiptypes

let rec build_term : Jv.t -> term -> Jv.t =
 fun ctx t ->
  match t with
  | Plus (a, b) ->
    (* Brr.Console.(log [str "zz1"; ctx; build_term ctx a]); *)
    Jv.call (build_term ctx a) "add" [| build_term ctx b |]
    (* Jv.call ctx "Add" [| build_term ctx a; build_term ctx b |] *)
  | Minus (a, b) -> Jv.call (build_term ctx a) "sub" [| build_term ctx b |]
  | Num n ->
    (* Jv.of_int n *)
    Jv.call (Jv.get ctx "Int") "const" [| Jv.of_int n |]
  | Var s ->
    (* TODO may have to keep track of bindings... *)
    (* Brr.Console.(
       log [str "zz"; Jv.get ctx "Int"; Jv.get (Jv.get ctx "Int") "const"]); *)
    Jv.call (Jv.get ctx "Int") "const" [| Jv.of_string s |]
  | UNIT | TList _ | TTupple _ -> failwith ""

let build_op : Jv.t -> bin_op -> term -> term -> Jv.t =
 fun ctx op a b ->
  match op with
  | EQ -> Jv.call (build_term ctx a) "eq" [| build_term ctx b |]
  | GT -> Jv.call (build_term ctx a) "gt" [| build_term ctx b |]
  | GTEQ -> Jv.call (build_term ctx a) "ge" [| build_term ctx b |]
  | LT -> Jv.call (build_term ctx a) "lt" [| build_term ctx b |]
  | LTEQ -> Jv.call (build_term ctx a) "le" [| build_term ctx b |]

let rec build_fml : pi -> Jv.t -> Jv.t =
 fun pi ctx ->
  match pi with
  | And (a, b) ->
    Jv.apply (Jv.get ctx "And") [| build_fml a ctx; build_fml b ctx |]
  | Or (a, b) ->
    Jv.apply (Jv.get ctx "Or") [| build_fml a ctx; build_fml b ctx |]
  | Not a -> Jv.apply (Jv.get ctx "Not") [| build_fml a ctx |]
  | Imply (a, b) ->
    Jv.apply (Jv.get ctx "Implies") [| build_fml a ctx; build_fml b ctx |]
  | True -> Jv.of_bool true
  | False -> Jv.of_bool false
  | Atomic (op, a, b) -> build_op ctx op a b
  | Predicate (_, _) -> failwith "not implemented"
(* | Or (a, b) -> Jv.apply (Jv.get ctx "Or") [| (build_fml a ctx ); (build_fml b ctx ) |] *)
(* ctx *)

(* let solve () =
   Console.(log [str "calling solve from ocaml1"]);
   (* Console.(log [Jv.get Jv.global "z3"]) *)
   (* ; *)
   let f = build_fml (And (True, True)) in
   let k sat = Console.(log [str ("ocaml: sat? " ^ string_of_bool sat)]) in
   Jv.apply
     (Jv.get (Jv.get Jv.global "z3") "solve")
     [| Jv.callback ~arity:1 f; Jv.callback ~arity:1 k |]
   |> ignore *)

open Effect
open Effect.Deep

type _ Effect.t += Ask : pi -> bool t

let askZ3 v = perform (Ask v)
let valid p = not (askZ3 (Not p))
let entails_exists _ _ _ = true
let normalPure p = p

let handle f =
  try_with f ()
    {
      effc =
        (fun (type a) (eff : a t) ->
          match eff with
          | Ask pi ->
            Some
              (fun (k : (a, _) continuation) ->
                let f ctx = build_fml pi ctx in
                let k1 sat =
                  (* print_endline "got result!!"; *)
                  continue k sat
                in
                (Jv.call (Jv.get Jv.global "z3") "solve")
                  [| Jv.callback ~arity:1 f; Jv.callback ~arity:1 k1 |]
                |> ignore)
          | _ -> None);
    }
