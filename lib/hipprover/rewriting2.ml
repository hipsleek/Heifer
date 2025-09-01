open Hipcore_typed
open Typedhip
open Pretty

type ('matched_value, 'k, 'k_result) pattern =
  | T of ('matched_value -> 'k -> 'k_result)

let __ = T (fun x k -> k x)
let drop = T (fun _ k -> k)

let as__ (T f1) =
  T
    (fun x k ->
      let k = f1 x (k x) in
      k)

exception Match_failure of string

let fail fmt = Format.kasprintf (fun s -> raise (Match_failure s)) fmt

(* let const ?to_s v =
  T
    (fun x k ->
      if x = v then k
      else
        match to_s with
        | None -> fail "could not match constant"
        | Some to_s ->
          fail "could not match constant; expected %s but got %s" (to_s v)
            (to_s x)) *)

(* weak type variables...? *)
(* let true1 = const ~to_s:string_of_pi True *)

let string s = T (fun x k -> if String.equal x s then k else fail "string")
let binder = string
let true_ = T (fun x k -> match x with True -> k | _ -> fail "true")
let false_ = T (fun x k -> match x with False -> k | _ -> fail "false")
let emp = T (fun x k -> match x with EmptyHeap -> k | _ -> fail "true")

let var s =
  T
    (fun x k ->
      match x.term_desc with Var s1 when String.equal s s1 -> k | _ -> fail "false")

let eq (T pt1) (T pt2) =
  T
    (fun x k ->
      match x with
      | Atomic (EQ, t1, t2) ->
        let k = pt1 t1 k in
        let k = pt2 t2 k in
        k
      | _ -> fail "false")

let seq (T pf1) (T pf2) =
  T
    (fun x k ->
      match x with
      | Sequence (f1, f2) ->
        let k = pf1 f1 k in
        let k = pf2 f2 k in
        k
      | _ -> fail "could not match Sequence; got %s" (string_of_staged_spec x))

let bind (T px1) (T pf1) (T pf2) =
  T
    (fun x k ->
      match x with
      | Bind (x1, f1, f2) ->
        let k = px1 x1 k in
        let k = pf1 f1 k in
        let k = pf2 f2 k in
        k
      | _ -> fail "bind")

let forall (T pv) (T pf) =
  T
    (fun x k ->
      match x with
      | ForAll (v, f) ->
        let k = pv v k in
        let k = pf f k in
        k
      | _ -> fail "could not match ForAll; got %s" (string_of_staged_spec x))

let exists (T pv) (T pf) =
  T
    (fun x k ->
      match x with
      | Exists (v, f) ->
        let k = pv v k in
        let k = pf f k in
        k
      | _ -> fail "could not match Exists; got %s" (string_of_staged_spec x))

let and_ (T pp1) (T pp2) =
  T
    (fun x k ->
      match x with
      | And (p1, p2) ->
        let k = pp1 p1 k in
        let k = pp2 p2 k in
        k
      | _ -> fail "could not match And; got %s" (string_of_pi x))

let req (T pp) (T ph) =
  T
    (fun x k ->
      match x with
      | Require (p, h) ->
        let k = pp p k in
        let k = ph h k in
        k
      | _ -> fail "could not match Require; got %s" (string_of_staged_spec x))

let ens (T pp) (T ph) =
  T
    (fun x k ->
      match x with
      | NormalReturn (p, h) ->
        let k = pp p k in
        let k = ph h k in
        k
      | _ ->
        fail "could not match NormalReturn; got %s" (string_of_staged_spec x))

let disj (T pf1) (T pf2) =
  T
    (fun x k ->
      match x with
      | Disjunction (f1, f2) ->
        let k = pf1 f1 k in
        let k = pf2 f2 k in
        k
      | _ ->
        fail "could not match Disjunction; got %s" (string_of_staged_spec x))

let reset (T pf) (T pcont) =
  T
    (fun x k ->
      match x with
      | Reset (f, cont) ->
        let k = pf f k in
        let k = pcont cont k in
        k
      | _ -> fail "could not match Reset; got %s" (string_of_staged_spec x))

let shift (T pshift) (T pxb) (T pfb) (T pxk) (T pfk) =
  T
    (fun x k ->
      match x with
      | Shift (is_shift, xb, fb, xk, fk) ->
        let k = pshift is_shift k in
        let k = pxb xb k in
        let k = pfb fb k in
        let k = pxk xk k in
        let k = pfk fk k in
        k
      | _ -> fail "cound not match Shift; got %s" (string_of_staged_spec x))

let rewrite_rooted ~lhs:(T p) ~target ~rhs = p target rhs
let match_ ~pat ~scr ~rhs = rewrite_rooted ~target:scr ~lhs:pat ~rhs
let match1 pat target = rewrite_rooted ~lhs:pat ~rhs:Fun.id ~target
let match2 pat target = rewrite_rooted ~lhs:pat ~rhs:(fun a b -> (a, b)) ~target

let match3 pat target =
  rewrite_rooted ~lhs:pat ~rhs:(fun a b c -> (a, b, c)) ~target

let%expect_test "match" =
  (* in the general case, matching is just rewrite_rooted *)
  let res =
    match_ ~pat:(and_ __ true_) ~scr:(And (True, True)) ~rhs:(fun a -> a)
  in
  Format.printf "%s@." (string_of_pi res);
  [%expect {| T |}];

  let res = match1 (and_ __ true_) (And (True, True)) in
  Format.printf "%s@." (string_of_pi res);
  [%expect {| T |}]

let%expect_test "rewrite" =
  let res = rewrite_rooted ~lhs:true_ ~rhs:False ~target:True in
  Format.printf "%s@." (string_of_pi res);
  [%expect {| F |}];

  let res =
    rewrite_rooted ~lhs:(and_ true_ __)
      ~rhs:(fun a -> And (a, True))
      ~target:(And (True, False))
  in
  Format.printf "%s@." (string_of_pi res);
  [%expect {| F/\T |}];

  let res =
    rewrite_rooted ~lhs:(and_ __ __)
      ~rhs:(fun a b -> And (b, a))
      ~target:(And (True, False))
  in
  Format.printf "%s@." (string_of_pi res);
  [%expect {| F/\T |}]

let pi_visitor lhs krhs =
  object (_self)
    inherit [_] map_spec as super

    method! visit_pi () s =
      let s1 = super#visit_pi () s in
      try rewrite_rooted ~lhs ~target:s1 ~rhs:krhs
      with Match_failure _ ->
        (* TODO do something with the msg? *)
        s1
  end

let staged_visitor lhs krhs =
  object (_self)
    inherit [_] map_spec as super

    method! visit_staged_spec () s =
      let s1 = super#visit_staged_spec () s in
      try rewrite_rooted ~lhs ~target:s1 ~rhs:krhs with Match_failure _ -> s1
  end

(** aka the type of "rewrite_all functions". It works for all ['k], which is the
    continuation used for rewriting to create the "small" ['s] terms. *)
type ('l, 's) rewriter = { rew : 'k. ('s, 'k, 's) pattern -> 'k -> 'l -> 'l }
[@@unboxed]

(* this just unboxes the single field *)
let rewrite_all { rew } lhs rhs target = rew lhs rhs target

let pi_in_staged : (staged_spec, pi) rewriter =
  {
    rew =
      (fun lhs krhs target -> (pi_visitor lhs krhs)#visit_staged_spec () target);
  }

let pi_in_pi : (pi, pi) rewriter =
  { rew = (fun lhs krhs target -> (pi_visitor lhs krhs)#visit_pi () target) }

let staged : (staged_spec, staged_spec) rewriter =
  {
    rew =
      (fun lhs krhs target ->
        (staged_visitor lhs krhs)#visit_staged_spec () target);
  }

let%expect_test "rewrite all" =
  let target = Syntax.(ens ~p:(And (True, False)) ()) in
  let r =
    (rewrite_all pi_in_staged (and_ true_ __) (fun a -> And (a, True))) target
  in
  Format.printf "%s@." (string_of_staged_spec r);
  [%expect {| ens F/\T |}]

type ('a, 'k) rule = ('a, 'k, 'a) pattern * 'k

type (_, _) database =
  | [] : ('a, unit) database
  | ( :: ) : ('a, 'k) rule * ('a, 'elts) database -> ('a, 'k -> 'elts) database

let rec to_fixed_point f ctx x =
  let x1 = f ctx x in
  (* TODO does the map visitor allow us to exploit ==? *)
  if x1 = x then x else to_fixed_point f ctx x1

let rec to_fixed_point2_rew r a b x =
  let x1 = rewrite_all r a b x in
  if x1 = x then x else to_fixed_point2_rew r a b x1

let rec autorewrite_once : type k.
    ('l, 's) rewriter -> ('s, k) database -> 'l -> 'l =
 fun rewrite_all db target ->
  match db with
  | [] -> target
  | (pat, rhs) :: db1 ->
    (* the reason we need the rewriter to work for all 'k: we need to instantiate it with the k that is in scope here. *)
    let target = to_fixed_point2_rew rewrite_all pat rhs target in
    autorewrite_once rewrite_all db1 target

(** Given the rule db, use each rule until it no longer changes, finish all the
    rules (this is what [autorewrite_once] does), then repeat from the top if
    there was some change *)
let autorewrite : type k. ('l, 's) rewriter -> ('s, k) database -> 'l -> 'l =
 fun rewrite_all db target ->
  to_fixed_point (autorewrite_once rewrite_all) db target

let%expect_test _ =
  let rule1 : (pi, _) rule = (and_ true_ __, fun a -> a) in
  let rule2 : (pi, _) rule = (and_ false_ __, fun _ -> False) in
  let db : _ database = [rule1; rule2] in
  let r = autorewrite pi_in_pi db (And (True, And (True, False))) in
  Format.printf "%s@." (string_of_pi r);
  [%expect {| F |}];

  let r = autorewrite pi_in_staged db Syntax.(ens ~p:(And (True, False)) ()) in
  Format.printf "%s@." (string_of_staged_spec r);
  [%expect {| ens F |}]
