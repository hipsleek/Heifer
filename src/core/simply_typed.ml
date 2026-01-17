open Syntax

let rec is_pure_term = function
  | Var _ -> true
  | Symbol _ -> true
  | Unit -> true
  | True -> true
  | False -> true
  | Int _ -> true
  | Fun _ -> true
  | Tuple _ -> true
  | Binop (_, t1, t2) -> is_pure_term t1 && is_pure_term t2
  | Unop (_, t) -> is_pure_term t
  | Nil -> true
  | Conj (t1, t2) -> is_pure_term t1 && is_pure_term t2
  | Disj (t1, t2) -> is_pure_term t1 && is_pure_term t2
  | Implies (t1, t2) -> is_pure_term t1 && is_pure_term t2
  | _ -> false

(** TODO: rewrite this to be more robust *)
let is_prop = function
  | True
  | False
  | Binop _
  (* binary and unary operators that return bool can be treated as prop *)
  | Unop _
  | Conj _
  | Disj _
  | Implies _
  | Subsumes _
  | Forall _
  | Exists _ -> true
  | _ -> false

let is_hprop = function
  | Emp | PointsTo _ | SepConj _ -> true (* forall? exists? *)
  | _ -> false

let check_sort t =
  let is_term x = x = Sort_term in
  let is_prop x = x = Sort_prop in
  let is_hprop x = x = Sort_hprop in
  let is_staged_spec x = x = Sort_staged_spec in
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
    | Binop ((Eq | Le | Lt | Ge | Gt | Neq), t1, t2) ->
        let* s1 = check_sort_aux env t1 in
        let* s2 = check_sort_aux env t2 in
        let* () = require (is_term s1 && is_term s2) "expected term in binop" in
        Ok Sort_prop
    | Binop ((Minus | Plus | Times | Cons), t1, t2) ->
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
        Ok Sort_staged_spec
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
        else if is_hprop s1 && is_hprop s2 then Ok Sort_hprop
        else if is_staged_spec s1 && is_staged_spec s2 then Ok Sort_staged_spec
        else Error "ill-sorted conjunction"
    | Disj (t1, t2) ->
        let* s1 = check_sort_aux env t1 in
        let* s2 = check_sort_aux env t2 in
        if is_prop s1 && is_prop s2 then Ok Sort_prop
        else if is_hprop s1 && is_hprop s2 then Ok Sort_hprop
        else if is_staged_spec s1 && is_staged_spec s2 then Ok Sort_staged_spec
        else Error "ill-sorted disjunction"
    | Forall b | Exists b ->
        let xs, body = Bindlib.unmbind b in
        let env' =
          Array.fold_left (fun e x -> TVMap.add x Sort_term e) env xs
        in
        let* s = check_sort_aux env' body in
        (match s with
        | Sort_prop | Sort_staged_spec | Sort_hprop -> Ok s
        | _ -> Error "ill-sorted quantifier body")
  in
  check_sort_aux TVMap.empty t
