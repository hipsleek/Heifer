open Bindlib
open Core.Syntax

type cont =
  | Nil
  | Cons_sequence of term * cont
  | Cons_bind of (term, term) binder * cont

let rec box_refine_box_cont tb = function
  | Nil -> tb
  | Cons_sequence (t, k) -> Mk.sequence tb (box_refine_cont t k)
  | Cons_bind (b, k) ->
      let x, t = unbind b in
      Mk.bind tb (bind_var x (box_refine_cont t k))

and box_refine_cont t = box_refine_box_cont (box_term t)

let box_refine_cont_reset t k = Mk.reset (box_refine_cont t k)
let refine_cont t k = unbox (box_refine_cont t k)
let refine_cont_reset t k = Reset (refine_cont t k)
let ignored_arg = new_tvar "_"

let captured_nil =
  let x = new_tvar "x" in
  unbox (Mk.fun_ (bind_mvar [| x |] (Mk.var x)))

let capture_cont_with f = function
  | Nil -> captured_nil
  | Cons_sequence (t, k) -> unbox (Mk.fun_ (bind_mvar [| ignored_arg |] (f t k)))
  | Cons_bind (b, k) ->
      let x, t = unbind b in
      unbox (Mk.fun_ (bind_mvar [| x |] (f t k)))

let capture_cont = capture_cont_with box_refine_cont
let capture_cont_reset = capture_cont_with box_refine_cont_reset
