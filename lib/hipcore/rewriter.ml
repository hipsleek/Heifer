(** Library for more ergonomic term rewriting. *)

(* tldr: we have ppxlib at home *)


open Typedhip

(** a pattern that matches against variables a, b, ... found in type ctx is modeled using ('ctx, 'a -> 'b -> ... -> 'result, 'result) *)
type ('ctx, 'k, 'result) pattern = 'ctx -> 'k -> 'result

(* another way to think about this type is as ('context, 'new_continuation, 'old_continuation).
   matching against a value of type a means we need to add a parameter of type a to the continuation,
   which the type ('ctx, 'a -> 'res, 'res) pattern models *)


(* things we want:
  - find and replace *)

exception Match_failed

let match_on ~(pat : ('a, 'b, 'c) pattern) (ctx : 'a) = pat ctx

let matches ~(pat : ('a, 'b, 'c) pattern) (ctx : 'a) = 
  try
    let  _ = ignore (pat ctx) [@ocaml.warning "-5"] in true 
  with
  | Match_failed -> false

(* basic combinators *)

let any : ('a, 'a -> 'b, 'b) pattern =
  fun ctx cont -> cont ctx

let nothing : ('a, 'b, 'b) pattern = fun _ cont -> cont

let capture (pat : ('ctx, 'k, 'result) pattern) : ('ctx, 'ctx -> 'k, 'result) pattern =
  fun ctx cont -> (pat ctx (cont ctx))  

let combine (pat : ('ctx, 'a -> 'b -> 'k, 'result) pattern) : ('ctx, ('a * 'b) -> 'k, 'result) pattern =
  fun ctx cont -> pat ctx (fun a b -> cont (a, b))

let optional (pat : ('ctx, 'a -> 'k, 'result) pattern) : ('ctx, 'a option -> 'k, 'result) pattern =
  fun ctx cont ->
    try
      (pat ctx) (fun a -> cont (Some a))
    with
    | Match_failed -> cont None

let filter (pat : ('ctx, 'a -> 'k, 'result) pattern) ~(f : 'a -> bool) : ('ctx, 'a -> 'k, 'result) pattern =
  fun ctx cont ->
    (pat ctx) (fun a -> if (f a) then cont a else raise Match_failed)

let invert (pat : ('ctx, 'k, 'result) pattern) : ('ctx, 'ctx -> 'result, 'result) pattern =
  any |> filter ~f:(fun ctx -> not (matches ~pat ctx))

let or_ (a : ('ctx, 'k, 'result) pattern) (b : ('ctx, 'k, 'result) pattern) =
  fun ctx cont -> try
        let result = a ctx cont in
        result
  with
    | Match_failed -> b ctx cont

let one_of (pats : ('ctx, 'k, 'result) pattern list) : ('ctx, 'k, 'result) pattern =
  let error : ('ctx, 'k, 'result) pattern = fun _ -> raise Match_failed in
  List.fold_right or_ pats error

let map (pat : ('ctx, 'a -> 'k, 'result) pattern) ~(f : 'a -> 'b) : ('ctx, 'b -> 'k, 'result) pattern =
  fun ctx cont -> pat ctx (fun a -> cont (f a))

(* ast matchers *)

module Ast_matchers = struct

  (* heap formula matchers *)
  let emp : (kappa, 'res, 'res) pattern = function
    | EmptyHeap -> (fun f -> f)
    | _ -> raise Match_failed

  let sep_conj (lhs : (kappa, 'a, 'b) pattern) (rhs : (kappa, 'b, 'c) pattern) : (kappa, 'a, 'c) pattern =
    fun heap_formula -> begin match heap_formula with
    | SepConj (l, r) -> (fun cont -> cont |> lhs l |> rhs r)
    | _ -> raise Match_failed
    end

  (* term matchers *)
  let num (pat : (int, 'k, 'res) pattern) : (const, 'k, 'res) pattern = function
    | Num n -> (match_on ~pat n)
    | _ -> raise Match_failed

  let tstr : (const, string -> 'res, 'res) pattern = function
    | TStr s -> (fun f -> f s)
    | _ -> raise Match_failed

  let ttrue : (const, 'res, 'res) pattern = function
    | TTrue -> (fun f -> f)
    | _ -> raise Match_failed

  let tfalse : (const, 'res, 'res) pattern = function
    | TFalse -> (fun f -> f)
    | _ -> raise Match_failed

  let constant (pat : (const, 'k, 'res) pattern) : (term, 'k, 'res) pattern = fun t ->
    match t.term_desc with
    | Const c -> (match_on ~pat c)
    | _ -> raise Match_failed

  let var (pat : (string, 'k, 'res) pattern) : (term, 'k, 'res) pattern = fun t ->
    match t.term_desc with
    | Var v -> (match_on ~pat v)
    | _ -> raise Match_failed

  let sconcat : (bin_term_op, 'res, 'res) pattern = function
    | SConcat -> (fun f -> f)
    | _ -> raise Match_failed

  let minus : (bin_term_op, 'res, 'res) pattern = function
    | Minus -> (fun f -> f)
    | _ -> raise Match_failed

  let plus : (bin_term_op, 'res, 'res) pattern = function
    | Plus -> (fun f -> f)
    | _ -> raise Match_failed

  let ttimes : (bin_term_op, 'res, 'res) pattern = function
    | TTimes -> (fun f -> f)
    | _ -> raise Match_failed

  let tdiv : (bin_term_op, 'res, 'res) pattern = function
    | TDiv -> (fun f -> f)
    | _ -> raise Match_failed


  let bin_op (op : (bin_term_op, 'a, 'b) pattern) (lhs : (term, 'b, 'c) pattern) 
    (rhs : (term, 'c, 'd) pattern) : (term, 'a, 'd) pattern =
    fun term -> match term.term_desc with
    | BinOp (o, l, r) -> (fun cont -> cont |> op o |> lhs l |> rhs r)
    | _ -> raise Match_failed

  let bin_op_typed (typ : (typ, 'z, 'a) pattern) (op : (bin_term_op, 'a, 'b) pattern) (lhs : (term, 'b, 'c) pattern) 
    (rhs : (term, 'c, 'd) pattern) : (term, typ -> 'a, 'd) pattern =
    fun term -> match term.term_desc with
    | BinOp (o, l, r) -> (fun cont -> cont |> typ term.term_type |> op o |> lhs l |> rhs r)
    | _ -> raise Match_failed

  let eq : (bin_rel_op, 'a, 'a) pattern = function
    | EQ -> (fun f -> f)
    | _ -> raise Match_failed

  let atom (rel_op : (bin_rel_op, 'a, 'b) pattern)
    (lhs : (term, 'b, 'c) pattern)
    (rhs : (term, 'c, 'd) pattern) : (pi, 'a, 'd) pattern =
      fun ctx cont -> match ctx with
      | Atomic (b, l, r) -> cont |> rel_op b |> lhs l |> rhs r
      | _ -> raise Match_failed

  let ptrue : (pi, 'a, 'b) pattern = fun p ->
    match p with
    | True -> (fun f -> f)
    | _ -> raise Match_failed

  let pfalse : (pi, 'a, 'b) pattern = function
    | False -> (fun f -> f)
    | _ -> raise Match_failed

  let pnot (pat : (pi, 'a, 'b) pattern) : (pi, 'a, 'b) pattern =
    fun p -> match p with
    | Not a -> (match_on ~pat a)
    | _ -> raise Match_failed

  let pand (lhs : (pi, 'a, 'b) pattern) (rhs : (pi, 'b, 'c) pattern) : (pi, 'a, 'c) pattern =
    fun p -> 
      match p with
    | And (l, r) -> (fun cont -> cont |> lhs l |> rhs r)
    | _ -> raise Match_failed

  let por (lhs : (pi, 'a, 'b) pattern) (rhs : (pi, 'b, 'c) pattern) : (pi, 'a, 'c) pattern =
    fun p -> match p with
    | Or (l, r) -> (fun cont -> cont |> lhs l |> rhs r)
    | _ -> raise Match_failed
end

module Ast_builders = struct
  let num n = {term_desc = Const (Num n); term_type = Int}
  let tstr s = {term_desc = Const (TStr s); term_type = TyString}
  let ttimes lhs rhs = {term_desc = BinOp (TTimes, lhs, rhs); term_type = Int}
  let minus lhs rhs = {term_desc = BinOp (Minus, lhs, rhs); term_type = Int}
  let plus lhs rhs = {term_desc = BinOp (Plus, lhs, rhs); term_type = Int}
  let tdiv lhs rhs = {term_desc = BinOp (TDiv, lhs, rhs); term_type = Int}
  let bin_op op lhs rhs ~typ = {term_desc = BinOp (op, lhs, rhs); term_type = typ}
end

type ('k, 'res) ast_matcher = {
  term_matchers: (term, 'k, 'res) pattern list
}

type 'ctx rewriter = 'ctx -> 'ctx

let make_rewriter (pat : ('ctx, 'k, 'term) pattern) (output : 'k) =
  fun ctx -> 
    try
      pat ctx output
    with
    | Match_failed -> ctx

type ast_rewriters = {
  term_rewriters: term rewriter list;
  kappa_rewriters: kappa rewriter list;
  pi_rewriters: pi rewriter list
}

let default_rewriters = {
  term_rewriters = [];
  kappa_rewriters = [];
  pi_rewriters = []
}

let rewriter_visitor (rewriters : ast_rewriters) =
  object
    inherit [_] map_normalised as super
    method! visit_term () term =
      let term = super#visit_term () term in
      List.fold_left (fun term rewriter -> rewriter term) term rewriters.term_rewriters

    method! visit_kappa () k =
      let k = super#visit_kappa () k in
      List.fold_left (fun kappa rewriter -> rewriter kappa) k rewriters.kappa_rewriters

    method! visit_pi () p =
      let p = super#visit_pi () p in
      let result = List.fold_left (fun pi rewriter -> rewriter pi) p rewriters.pi_rewriters in
      result
  end

let rec apply_rewrites (rewriter : 'b -> 'b) (target : 'b) : 'b =
  let result = rewriter target in
  if result = target
  then result
  else apply_rewrites rewriter result

let rewrite_kappa (rewriters : ast_rewriters) (kappa : kappa) =
  apply_rewrites ((rewriter_visitor rewriters)#visit_kappa ()) kappa

let rewrite_term (rewriters : ast_rewriters) (t : term) =
  apply_rewrites ((rewriter_visitor rewriters)#visit_term ()) t

let rewrite_pi (rewriters : ast_rewriters) (p : pi) =
  apply_rewrites ((rewriter_visitor rewriters)#visit_pi ()) p

let%expect_test "matching" =
  let open Ast_matchers in
  let expr = {term_desc = BinOp (Plus, {term_desc = Const (Num 5); term_type = Int}, {term_desc = Const (Num 6); term_type = Int}); term_type = Int} in
  let k = match_on ~pat:(bin_op plus (constant (num any)) (constant (num any))) expr in
  k (fun a b -> Printf.printf "matched against %d %d" a b);
  [%expect {| matched against 5 6 |}];
  let k = match_on ~pat:(bin_op plus (constant (num any)) nothing) expr in
  k (fun a -> Printf.printf "matched against %d" a);
  [%expect {| matched against 5 |}]

let%expect_test "matching logical formula" =
  let open Ast_matchers in
  let open Pretty_typed in
  let var s = {term_desc = Var s; term_type = Int} in
  let expr = And (And (True, Atomic(EQ, var "x", var "y")), True) in
  let k = match_on ~pat:(one_of [pand any ptrue; pand ptrue any; por any pfalse; por pfalse any]) expr in
  k (fun p -> Printf.printf "matched against %s" (string_of_pi p));
  [%expect {| matched against T/\x=y |}]
  
let%expect_test "rewriting" =
  let rewrites = Ast_matchers.{default_rewriters with
    pi_rewriters = [
      make_rewriter (one_of [pand any ptrue; pand ptrue any;
        por any pfalse; por pfalse any])
      (fun t -> t);
    ]
  } in
  let var s = {term_desc = Var s; term_type = Int} in
  let p = And (And (True, Atomic(EQ, var "x", var "y")), True) in
  let result = rewrite_pi rewrites p in
  Printf.printf " rewrite result: %s " (Pretty_typed.string_of_pi result);
  [%expect {| rewrite result: x=y |}]

let rec split_into_conjuncts (p : pi) : pi list =
  match p with
  | And (p1, p2) -> (split_into_conjuncts p1) @ (split_into_conjuncts p2)
  | _ -> [p]
