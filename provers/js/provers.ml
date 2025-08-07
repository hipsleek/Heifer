open Hipcore_typed
open Hipcore.Common
open Typedhip
open Provers_common

(*
https://github.com/Z3Prover/z3/blob/master/src/api/js/examples/high-level/miracle-sudoku.ts
https://microsoft.github.io/z3guide/programming/Z3%20JavaScript%20Examples/
*)

(*
x = ctx.Int.const('x')
s = new ctx.Solver()
s.add(ctx.Int.const('x').eq(1))
r = await s.check()
+s.model().eval(x)

s = new ctx.Solver()
a = ctx.Int.const('a')
s.add(ctx.Exists([a], a.eq(1)))
r = await s.check()
*)

let rec build_term : Jv.t -> term -> Jv.t =
 fun ctx t ->
  match t.term_desc with
    | Const (TStr _) -> failwith "nyi"
    | BinOp (SConcat, _, _) -> failwith "nyi"
    | Rel (bop, a, b) ->
    (match bop with
    | EQ -> Jv.call (build_term ctx a) "eq" [| build_term ctx b |]
    | _ -> failwith "TODO")
  | BinOp (Plus, a, b) ->
    Jv.call (build_term ctx a) "add" [| build_term ctx b |]
    (* Jv.call ctx "Add" [| build_term ctx a; build_term ctx b |] *)
  | BinOp (Minus, a, b) -> Jv.call (build_term ctx a) "sub" [| build_term ctx b |]
  | Const (Num n) ->
    (* Jv.of_int n *)
    Jv.call (Jv.get ctx "Int") "val" [| Jv.of_int n |]
  | Var s -> Jv.call (Jv.get ctx "Int") "const" [| Jv.of_string s |]
  | Const ValUnit -> build_term ctx Syntax.(var "unit" ~typ:Unit)
  | Const Nil -> build_term ctx Syntax.(var "nil" ~typ:(TConstr ("list", [Int])))
  | Const TTrue -> Jv.call (Jv.get ctx "Bool") "val" [| Jv.of_bool true |]
  | Const TFalse -> Jv.call (Jv.get ctx "Bool") "val" [| Jv.of_bool false |]
  | TNot a -> Jv.apply (Jv.get ctx "Not") [| build_term ctx a |]
  | BinOp (TAnd, a, b) ->
    Jv.apply (Jv.get ctx "And") [| build_term ctx a; build_term ctx b |]
  | BinOp (TOr, a, b) ->
    Jv.apply (Jv.get ctx "Or") [| build_term ctx a; build_term ctx b |]
  | TApp _ -> failwith "?"
  | TLambda _ -> failwith "?"
  | Construct (_, _) | BinOp (TCons, _, _) | BinOp (TPower, _, _) | BinOp (TTimes, _, _) | BinOp (TDiv, _, _) | TTuple _ -> failwith "not yet implemented"

let build_op : Jv.t -> bin_rel_op -> term -> term -> Jv.t =
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
  | True ->
    Jv.call (Jv.get ctx "Bool") "val" [| Jv.of_bool true |]
    (* Jv.of_bool true *)
  | False ->
    (* Jv.of_bool false *)
    Jv.call (Jv.get ctx "Bool") "val" [| Jv.of_bool false |]
  | Atomic (op, a, b) -> build_op ctx op a b
  | Predicate (_, _) -> failwith "not implemented"
  | Subsumption (_, _) -> build_fml True ctx

open Effect
open Effect.Deep

(* function is from ctx to z3 expression *)
type _ Effect.t += Ask : (Jv.t -> Jv.t) -> bool t

let _askZ3 _env p =
  (* TODO make use of env *)
  perform (Ask (build_fml p))

let _valid p = not (_askZ3 SMap.empty (Not p))

(* check if p1 => ex vs. p2 is valid *)
let entails_exists p1 vs p2 =
  (* TODO make use of the typing environment *)
  let f ctx =
    Jv.apply (Jv.get ctx "Not")
      [|
        Jv.apply (Jv.get ctx "Implies")
          [|
            build_fml p1 ctx;
            (match vs with
            | [] -> build_fml p2 ctx
            | _ :: _ ->
              Jv.apply (Jv.get ctx "Exists")
                [|
                  Jv.of_list
                    (fun v ->
                      Jv.call (Jv.get ctx "Int") "const" [| Jv.of_string (ident_of_binder v) |])
                    vs;
                  build_fml p2 ctx;
                |]);
          |];
      |]
  in
  let valid = not (perform (Ask f)) in
  if valid then Valid else Invalid

let handle f =
  try_with f ()
    {
      effc =
        (fun (type a) (eff : a t) ->
          match eff with
          | Ask make_pi ->
            Some
              (fun (k : (a, _) continuation) ->
                let k1 sat = continue k sat in
                (Jv.call (Jv.get Jv.global "z3") "solve")
                  [| Jv.callback ~arity:1 make_pi; Jv.callback ~arity:1 k1 |]
                |> ignore)
          | _ -> None);
    }
