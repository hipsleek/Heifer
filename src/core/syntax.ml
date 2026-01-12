open Bindlib

type metavar = { mv_name : string }

(** User-defined symbol (top-level declaration). *)
type symbol = { sym_name : string }

type binop =
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Neq
  | Plus
  | Times
  | Cons

type unop =
  | Not
  | Neg

(** Atomic term: variables, (literal) constants, functions, primitives. We
    enforce that [term] must be pure: no side-effect can happen when reducing a
    term. *)
type term =
  | Var of term var
  | Symbol of symbol
  | Unit
  | True
  | False
  | Int of int
  | Fun of (term, term) mbinder
  (* | TApp of string * term list *)
  | Tuple of term list
  | Binop of binop * term * term
  | Unop of unop * term
  | Nil
  (* | PAtom of term *)
  | Conj of term * term
  | Disj of term * term
  | Implies of term * term
  (* | PForall of (term, term) mbinder *)
  | Subsumes of term * term
  (* | HPure of term *)
  | Emp
  | PointsTo of term * term
  | SepConj of term * term
  (* | Return of term *)
  | Requires of term
  | Ensures of term
  | Sequence of term * term
  | Bind of term * (term, term) binder
  | Apply of term * term list
  (* | Disjunct of term * term *)
  | Forall of (term, term) mbinder
  | Exists of (term, term) mbinder
  | Shift of (term, term) binder
  | Reset of term
(* | Dollar of term * (term, term) binder *)
(* | SMetavar of metavar *)

type def = (term, term) mbinder

(** Top level declaration.

    [Dfun] declares a possibly recursive function. *)
type decl = Dfun of symbol * def

(** Smart constructors that wrap data in [Bindlib.box]. *)
module Mk = struct
  let var = box_var
  let symbol sym = box (Symbol sym)
  let unit = box Unit
  let nil = box Nil
  let true_ = box True
  let false_ = box False
  let app = box_apply2 (fun f xs -> Apply (f, xs))
  let int i = box (Int i)
  let tuple = box_apply (fun ts -> Tuple ts)
  let fun_ = box_apply (fun b -> Fun b)
  let binop op = box_apply2 (fun t1 t2 -> Binop (op, t1, t2))
  let unop op = box_apply (fun t -> Unop (op, t))
  let conj = box_apply2 (fun p1 p2 -> Conj (p1, p2))
  let implies = box_apply2 (fun p1 p2 -> Implies (p1, p2))
  let subsumes = box_apply2 (fun f1 f2 -> Subsumes (f1, f2))
  let emp = box Emp
  let pointsto = box_apply2 (fun t1 t2 -> PointsTo (t1, t2))
  let sepconj = box_apply2 (fun p1 p2 -> SepConj (p1, p2))
  let requires = box_apply (fun p -> Requires p)
  let ensures = box_apply (fun p -> Ensures p)
  let sequence = box_apply2 (fun s1 s2 -> Sequence (s1, s2))
  let bind = box_apply2 (fun s b -> Bind (s, b))
  let apply = box_apply2 (fun f t -> Apply (f, t))
  let disj = box_apply2 (fun s1 s2 -> Disj (s1, s2))
  let forall = box_apply (fun b -> Forall b)
  let exists = box_apply (fun b -> Exists b)
  let shift = box_apply (fun b -> Shift b)
  let reset = box_apply (fun s -> Reset s)
end

module Constr = struct
  let foldr1 ?default f xs =
    let rec foldr1_aux f y = function
      | [] -> y
      | x :: xs -> f y (foldr1_aux f x xs)
    in
    match xs with
    | [] ->
        (match default with None -> failwith "foldr1: empty" | Some a -> a)
    | x :: xs -> foldr1_aux f x xs

  let sep_conj = foldr1 ~default:Emp (fun c t -> SepConj (c, t))
  let conj = foldr1 ~default:True (fun c t -> Conj (c, t))

  let seq xs =
    match xs with
    | [] -> failwith "seq: empty"
    | [x] -> x
    | _ -> foldr1 (fun c t -> Sequence (c, t)) xs

  let ens_seq h f = Sequence (Ensures h, f)
  let req_seq h f = Sequence (Ensures h, f)
end

let new_tvar = new_var (fun v -> Var v)

let rec box_term = function
  | Var x -> Mk.var x
  | Symbol sym -> Mk.symbol sym
  | Unit -> Mk.unit
  | Nil -> Mk.nil
  | True -> Mk.true_
  | False -> Mk.false_
  | Apply (f, xs) -> Mk.apply (box_term f) (box_list (List.map box_term xs))
  | Int i -> Mk.int i
  | Tuple ts -> Mk.tuple (box_list (List.map box_term ts))
  | Fun b -> Mk.fun_ (box_mbinder box_term b)
  | Binop (op, t1, t2) -> Mk.binop op (box_term t1) (box_term t2)
  | Unop (op, t) -> Mk.unop op (box_term t)
  | Conj (p1, p2) -> Mk.conj (box_term p1) (box_term p2)
  | Disj (p1, p2) -> Mk.disj (box_term p1) (box_term p2)
  | Implies (p1, p2) -> Mk.implies (box_term p1) (box_term p2)
  | Subsumes (f1, f2) -> Mk.subsumes (box_term f1) (box_term f2)
  | Emp -> Mk.emp
  | PointsTo (t1, t2) -> Mk.pointsto (box_term t1) (box_term t2)
  | SepConj (p1, p2) -> Mk.sepconj (box_term p1) (box_term p2)
  | Requires p -> Mk.requires (box_term p)
  | Ensures p -> Mk.ensures (box_term p)
  | Sequence (s1, s2) -> Mk.sequence (box_term s1) (box_term s2)
  | Bind (s, b) -> Mk.bind (box_term s) (box_binder box_term b)
  | Forall b -> Mk.forall (box_mbinder box_term b)
  | Exists b -> Mk.exists (box_mbinder box_term b)
  | Shift b -> Mk.shift (box_binder box_term b)
  | Reset s -> Mk.reset (box_term s)

(* Aliases for compatibility *)
let box_prop = box_term
let box_hprop = box_term
let box_staged_spec = box_term

type staged_spec = term
type prop = term
type hprop = term

type sort =
  | Sort_term
  | Sort_prop
  | Sort_hprop
  | Sort_staged_spec

module Sort = struct
  exception Invalid_sort of string
  exception Sort_mismatch of string

  let invalid_sort msg = raise (Invalid_sort msg)
  let sort_mismatch msg = raise (Sort_mismatch msg)
end

module TV = struct
  type t = term var

  let compare = compare_vars
end

(** Set and map of term variables. *)
module TVSet = Set.Make (TV)

module TVMap = Map.Make (TV)

module Sym = struct
  type t = symbol

  let compare sym1 sym2 = String.compare sym1.sym_name sym2.sym_name
end

(** Set and map of symbols. *)
module SymSet = Set.Make (Sym)

module SymMap = Map.Make (Sym)

let rec equal_term t1 t2 =
  match (t1, t2) with
  | Var x1, Var x2 -> eq_vars x1 x2
  | Symbol s1, Symbol s2 -> s1 = s2
  | Unit, Unit -> true
  | True, True -> true
  | False, False -> true
  | Int i1, Int i2 -> i1 = i2
  | Fun b1, Fun b2 -> eq_mbinder equal_term b1 b2
  | Apply (f1, xs1), Apply (f2, xs2) ->
      equal_term f1 f2
      && List.length xs1 = List.length xs2
      && List.for_all2 equal_term xs1 xs2
  | Tuple ts1, Tuple ts2 ->
      List.length ts1 = List.length ts2 && List.for_all2 equal_term ts1 ts2
  | Binop (op1, t11, t12), Binop (op2, t21, t22) ->
      op1 = op2 && equal_term t11 t21 && equal_term t12 t22
  | Unop (op1, t1), Unop (op2, t2) -> op1 = op2 && equal_term t1 t2
  | Nil, Nil -> true
  | Conj (p11, p12), Conj (p21, p22) -> equal_term p11 p21 && equal_term p12 p22
  | Disj (p11, p12), Disj (p21, p22) -> equal_term p11 p21 && equal_term p12 p22
  | Implies (p11, p12), Implies (p21, p22) ->
      equal_term p11 p21 && equal_term p12 p22
  | Subsumes (s11, s12), Subsumes (s21, s22) ->
      equal_term s11 s21 && equal_term s12 s22
  | Emp, Emp -> true
  | PointsTo (t11, t12), PointsTo (t21, t22) ->
      equal_term t11 t21 && equal_term t12 t22
  | SepConj (h11, h12), SepConj (h21, h22) ->
      equal_term h11 h21 && equal_term h12 h22
  | Requires h1, Requires h2 -> equal_term h1 h2
  | Ensures h1, Ensures h2 -> equal_term h1 h2
  | Sequence (s11, s12), Sequence (s21, s22) ->
      equal_term s11 s21 && equal_term s12 s22
  | Bind (s1, b1), Bind (s2, b2) ->
      equal_term s1 s2 && eq_binder equal_term b1 b2
  | Forall b1, Forall b2 -> eq_mbinder equal_term b1 b2
  | Exists b1, Exists b2 -> eq_mbinder equal_term b1 b2
  | Shift b1, Shift b2 -> eq_binder equal_term b1 b2
  | Reset s1, Reset s2 -> equal_term s1 s2
  | _, _ -> false

(* Aliases *)
let equal_prop = equal_term
let equal_hprop = equal_term
let equal_staged_spec = equal_term

let match_term ~var ~symbol ~unit ~true_ ~false_ ~int ~fun_ ~tuple ~binop ~unop
    ~nil ~apply t =
  match t with
  | Var x -> var x
  | Symbol s -> symbol s
  | Unit -> unit
  | True -> true_
  | False -> false_
  | Int i -> int i
  | Fun b -> fun_ b
  | Tuple l -> tuple l
  | Binop (o, l, r) -> binop o l r
  | Unop (o, r) -> unop o r
  | Nil -> nil
  | Apply (f, a) -> apply f a
  | _ -> failwith "match_term: mismatch"

let match_prop ~atom ~conj ~implies ~subsumes ~exists ~forall t =
  match t with
  | Conj (a, b) -> conj a b
  | Implies (a, b) -> implies a b
  | Subsumes (a, b) -> subsumes a b
  | Forall b -> forall b
  | Exists b -> exists b
  | Var _ | Symbol _ | Unit | True | False | Int _ | Fun _ | Tuple _ | Binop _
  | Unop _ | Nil | Apply _ ->
      atom t
  | _ -> failwith "match_prop: mismatch"

let match_hprop ~emp ~pointsto ~sepconj t =
  match t with
  | Emp -> emp
  | PointsTo (l, r) -> pointsto l r
  | SepConj (a, b) -> sepconj a b
  | _ -> failwith "match_hprop: mismatch"

let match_staged_spec ~return_ ~requires ~ensures ~sequence ~bind ~conj ~disj
    ~forall ~exists ~shift ~reset ~apply t =
  match t with
  | Requires p -> requires p
  | Ensures p -> ensures p
  | Sequence (a, b) -> sequence a b
  | Bind (a, b) -> bind a b
  | Conj (a, b) -> conj a b
  | Disj (a, b) -> disj a b
  | Forall b -> forall b
  | Exists b -> exists b
  | Shift b -> shift b
  | Reset a -> reset a
  | Apply (f, a) -> apply f a
  | _ -> return_ t

let rec dump_term ppf t =
  match t with
  | Sequence (a, b) ->
      Fmt.pf ppf "@[Sequence (%a, %a)@]" dump_term a dump_term b
  | Var x -> Fmt.pf ppf "@[Var %s@]" (Bindlib.name_of x)
  | Symbol s -> Fmt.pf ppf "@[Symbol %s@]" s.sym_name
  | Unit -> Fmt.string ppf "Unit"
  | True -> Fmt.string ppf "True"
  | False -> Fmt.string ppf "False"
  | Int i -> Fmt.pf ppf "@[Int %d@]" i
  | Fun b ->
      let xs, body = Bindlib.unmbind b in
      let args =
        String.concat " " (Array.to_list (Array.map Bindlib.name_of xs))
      in
      Fmt.pf ppf "@[Fun (%s. %a)@]" args dump_term body
  | Tuple ts ->
      Fmt.pf ppf "@[Tuple [%a]@]" (Fmt.list ~sep:Fmt.comma dump_term) ts
  | Binop (op, t1, t2) ->
      let op_s =
        match op with
        | Lt -> "Lt"
        | Le -> "Le"
        | Gt -> "Gt"
        | Ge -> "Ge"
        | Eq -> "Eq"
        | Neq -> "Neq"
        | Plus -> "Plus"
        | Times -> "Times"
        | Cons -> "Cons"
      in
      Fmt.pf ppf "@[Binop (%s, %a, %a)@]" op_s dump_term t1 dump_term t2
  | Unop (op, t) ->
      let op_s = match op with Not -> "Not" | Neg -> "Neg" in
      Fmt.pf ppf "@[Unop (%s, %a)@]" op_s dump_term t
  | Nil -> Fmt.string ppf "Nil"
  | Conj (t1, t2) -> Fmt.pf ppf "@[Conj (%a, %a)@]" dump_term t1 dump_term t2
  | Disj (t1, t2) -> Fmt.pf ppf "@[Disj (%a, %a)@]" dump_term t1 dump_term t2
  | Implies (t1, t2) ->
      Fmt.pf ppf "@[Implies (%a, %a)@]" dump_term t1 dump_term t2
  | Subsumes (t1, t2) ->
      Fmt.pf ppf "@[Subsumes (%a, %a)@]" dump_term t1 dump_term t2
  | Emp -> Fmt.string ppf "Emp"
  | PointsTo (t1, t2) ->
      Fmt.pf ppf "@[PointsTo (%a, %a)@]" dump_term t1 dump_term t2
  | SepConj (t1, t2) ->
      Fmt.pf ppf "@[SepConj (%a, %a)@]" dump_term t1 dump_term t2
  | Requires t -> Fmt.pf ppf "@[Requires (%a)@]" dump_term t
  | Ensures t -> Fmt.pf ppf "@[Ensures (%a)@]" dump_term t
  | Bind (s, b) ->
      let x, body = Bindlib.unbind b in
      Fmt.pf ppf "@[Bind (%a, %s. %a)@]" dump_term s (Bindlib.name_of x)
        dump_term body
  | Apply (f, ts) ->
      Fmt.pf ppf "@[Apply (%a, [%a])@]" dump_term f
        (Fmt.list ~sep:Fmt.comma dump_term)
        ts
  | Forall b ->
      let xs, body = Bindlib.unmbind b in
      let args =
        String.concat " " (Array.to_list (Array.map Bindlib.name_of xs))
      in
      Fmt.pf ppf "@[Forall (%s. %a)@]" args dump_term body
  | Exists b ->
      let xs, body = Bindlib.unmbind b in
      let args =
        String.concat " " (Array.to_list (Array.map Bindlib.name_of xs))
      in
      Fmt.pf ppf "@[Exists (%s. %a)@]" args dump_term body
  | Shift b ->
      let k, body = Bindlib.unbind b in
      Fmt.pf ppf "@[Shift (%s. %a)@]" (Bindlib.name_of k) dump_term body
  | Reset t -> Fmt.pf ppf "@[Reset (%a)@]" dump_term t

let is_term = function Sort_term -> true | _ -> false
let is_prop = function Sort_term | Sort_prop -> true | _ -> false
let is_hprop = function Sort_hprop -> true | _ -> false
let is_staged_spec _ = true

let check_sort t =
  let rec check_sort_aux env t =
    let open Result in
    let ( let* ) = bind in
    let require cond msg = if cond then Ok () else Error msg in
    match t with
    | Var x -> Ok (try TVMap.find x env with Not_found -> Sort_term)
    | Symbol _ | Unit | True | False | Int _ | Nil -> Ok Sort_term
    | Tuple ts ->
        let* () =
          List.fold_left
            (fun acc t ->
              let* () = acc in
              let* s = check_sort_aux env t in
              require (is_term s) "expected term in tuple")
            (Ok ()) ts
        in
        Ok Sort_term
    | Binop (_, t1, t2) ->
        let* s1 = check_sort_aux env t1 in
        let* s2 = check_sort_aux env t2 in
        let* () = require (is_term s1 && is_term s2) "expected term in binop" in
        Ok Sort_term
    | Unop (_, t) ->
        let* s = check_sort_aux env t in
        let* () = require (is_term s) "expected term in unop" in
        Ok Sort_term
    | Apply (f, args) ->
        let* sf = check_sort_aux env f in
        let* () = require (is_term sf) "expected term in apply function" in
        let* () =
          List.fold_left
            (fun acc t ->
              let* () = acc in
              let* s = check_sort_aux env t in
              require (is_term s) "expected term in apply arg")
            (Ok ()) args
        in
        Ok Sort_term
    | Fun b ->
        let xs, body = Bindlib.unmbind b in
        let env' =
          Array.fold_left (fun e x -> TVMap.add x Sort_term e) env xs
        in
        let* s = check_sort_aux env' body in
        let* () = require (is_term s) "expected term in function body" in
        Ok Sort_term
    | Emp -> Ok Sort_hprop
    | PointsTo (t1, t2) ->
        let* s1 = check_sort_aux env t1 in
        let* s2 = check_sort_aux env t2 in
        let* () =
          require (is_term s1 && is_term s2) "expected term in pointsto"
        in
        Ok Sort_hprop
    | SepConj (h1, h2) ->
        let* s1 = check_sort_aux env h1 in
        let* s2 = check_sort_aux env h2 in
        let* () =
          require (is_hprop s1 && is_hprop s2) "expected hprop in sepconj"
        in
        Ok Sort_hprop
    | Subsumes (t1, t2) ->
        let* s1 = check_sort_aux env t1 in
        let* s2 = check_sort_aux env t2 in
        let* () =
          require (is_term s1 && is_term s2) "expected term in subsumes"
        in
        Ok Sort_prop
    | Implies (p1, p2) ->
        let* s1 = check_sort_aux env p1 in
        let* s2 = check_sort_aux env p2 in
        let* () =
          require (is_prop s1 && is_prop s2) "expected prop in implies"
        in
        Ok Sort_prop
    | Requires p | Ensures p ->
        let* s = check_sort_aux env p in
        if is_prop s || is_hprop s then Ok Sort_staged_spec
        else Error "expected prop or hprop in requires/ensures"
    | Sequence (s1, s2) ->
        let* r1 = check_sort_aux env s1 in
        let* r2 = check_sort_aux env s2 in
        if is_staged_spec r1 && is_staged_spec r2 then Ok Sort_staged_spec
        else Error "expected staged spec in sequence"
    | Bind (s, b) ->
        let* r = check_sort_aux env s in
        let* () =
          require (is_staged_spec r) "expected staged spec in bind head"
        in
        let x, body = Bindlib.unbind b in
        let env' = TVMap.add x Sort_term env in
        let* s_body = check_sort_aux env' body in
        let* () =
          require (is_staged_spec s_body) "expected staged spec in bind body"
        in
        Ok Sort_staged_spec
    | Shift b ->
        let k, body = Bindlib.unbind b in
        let env' = TVMap.add k Sort_term env in
        let* s_body = check_sort_aux env' body in
        let* () =
          require (is_staged_spec s_body) "expected staged spec in shift body"
        in
        Ok Sort_staged_spec
    | Reset s ->
        let* s_res = check_sort_aux env s in
        let* () =
          require (is_staged_spec s_res) "expected staged spec in reset"
        in
        Ok Sort_staged_spec
    | Conj (t1, t2) ->
        let* s1 = check_sort_aux env t1 in
        let* s2 = check_sort_aux env t2 in
        if is_prop s1 && is_prop s2 then Ok Sort_prop
        else if is_staged_spec s1 && is_staged_spec s2 then Ok Sort_staged_spec
        else Error "ill-sorted conjunction"
    | Disj (t1, t2) ->
        let* s1 = check_sort_aux env t1 in
        let* s2 = check_sort_aux env t2 in
        if is_staged_spec s1 && is_staged_spec s2 then Ok Sort_staged_spec
        else Error "ill-sorted disjunction"
    | Forall b | Exists b ->
        let xs, body = Bindlib.unmbind b in
        let env' =
          Array.fold_left (fun e x -> TVMap.add x Sort_term e) env xs
        in
        let* s = check_sort_aux env' body in
        if is_prop s then Ok Sort_prop
        else if is_staged_spec s then Ok Sort_staged_spec
        else Error "ill-sorted quantifier body"
  in
  check_sort_aux TVMap.empty t
