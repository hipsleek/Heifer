open Hipcore_typed
open Typedhip
open Debug
(*
open Pretty
open Subst
*)

open Utils

(* shift-reset reduction rules. Technically we can put this in normalize.ml; but
   let's put this logic into a separate files for easy of understanding *)

(* a visitor *)
let shift_free () = Misc.todo ()

let reset_free () = Misc.todo ()

(* do we need this tho? Seems redundant! *)
let shift_reset_free () = Misc.todo ()

let ignored_cont_arg = "#ignored_arg"

let is_ignored_cont_binder (x : binder) : bool = ident_of_binder x = ignored_cont_arg

let compose_cont (f : staged_spec) (x : binder) (cont : staged_spec) : staged_spec =
  if is_ignored_cont_binder x then Sequence (f, cont) else Bind (x, f, cont)

(* reset (forall x. f) \entails forall x. reset f *)
(* only on the left *)
let norm_reset_all : _ Rewriting2.rule = Rewriting2.(
  reset (forall __ __) __ __,
  fun x f k cont -> ForAll (x, Reset (f, k, cont))
)

(* reset (exists x. f) \bientails exists x. reset f *)
(* bientails; both side of the proof *)
let norm_reset_ex : _ Rewriting2.rule = Rewriting2.(
  reset (exists __ __) __ __,
  fun x f k cont -> Exists (x, Reset (f, k, cont))
)

(* reset (f1 \/ f2) \bientails reset f1 \/ reset f2 *)
(* bientails; both side of the proof *)
let norm_reset_disj : _ Rewriting2.rule = Rewriting2.(
  reset (disj __ __) __ __,
  fun f1 f2 x cont -> Disjunction (Reset (f1, x, cont), Reset (f2, x, cont))
)

(* reset (ens Q; f) \bientails ens Q; reset f *)
(* bientails; both side of the proof *)
(* let norm_reset_seq_ens : _ Rewriting2.rule = Rewriting2.(
  reset (seq (ens __ __) __) __ __,
  fun p k f x cont -> Sequence (NormalReturn (p, k), Reset (f, x, cont))
)

(* reset (req H; f) \entails req H; reset f *)
(* entails; only on the left *)
let norm_reset_seq_req : _ Rewriting2.rule = Rewriting2.(
  reset (seq (req __ __) __) __ __,
  fun p k f x cont -> Sequence (Require (p, k), Reset (f, x, cont))
)

let norm_reset_bind_ens : _ Rewriting2.rule = Rewriting2.(
  reset (bind __ (ens __ __) __) __ __,
  fun x p k f xcont cont -> Bind (x, NormalReturn (p, k), Reset (f, xcont, cont))
)

let norm_reset_bind_req : _ Rewriting2.rule = Rewriting2.(
  reset (bind __ (req __ __) __) __ __,
  fun x p k f xcont cont -> Bind (x, Require (p, k), Reset (f, xcont, cont))
) *)

(* reset (ens Q) \bientails ens Q *)
(* both side of the proof *)
let norm_reset_ens : _ Rewriting2.rule = Rewriting2.(
  reset (ens __ __) __ __,
  fun p k x cont ->
    (* debug ~at:5 ~title:"norm_reset_ens" "ens (%s, %s), %s, %s"
      (Pretty.string_of_pi p)
      (Pretty.string_of_kappa k)
      (Pretty.string_of_binder x)
      (Pretty.string_of_staged_spec cont); *)
    let cont = match cont with
      | NormalReturn _ ->
          cont
      | _ ->
          let res_var_typed = Syntax.var "res" in
          let new_x = Variables.fresh_variable ~v:"x" "continuation" in
          let new_x_typed = Syntax.var new_x ~typ:res_var_typed.term_type in
          let new_cont = NormalReturn (Syntax.eq res_var_typed new_x_typed, EmptyHeap) in
          Reset (cont, (new_x, Any), new_cont)
    in
    compose_cont (NormalReturn (p, k)) x cont
)

(* both sides *)
let shift_reset_normalization_rules_both : _ Rewriting2.database = [
  norm_reset_ex;
  norm_reset_disj;
  (* norm_reset_seq_ens; *)
  (* norm_reset_bind_ens; *)
  norm_reset_ens;
]

(* lhs only *)
let shift_reset_normalization_rules_lhs_only : _ Rewriting2.database = [
  norm_reset_all;
  (* norm_reset_seq_req; *)
  (* norm_reset_bind_req; *)
]

(* we need a more "structure" way to compose the continuation *)
(* if the continuation is identity, we completely replace the continuation with the new continuation.
   but this can be handled by the normalization to rewrite the redundant equality away *)
(* if the continuation takes an argument, then we need to connect the old continuation with the new stage
   by a "bind" *)
(* if the continuation does not take an argument, then we connect the old continuation with the new stage
   by a "seq" *)

(* accumulate/build the continuation; with seq *)
(* reset (shift body cont; f) -> reset (shift body (cont; f)) *)
let red_bind_shift_extend : _ Rewriting2.rule = Rewriting2.(
  bind __ (shift __ __ __ __ __) __,
  fun x_bind is_shift x_body f_body x_cont f_cont f ->
    Shift (is_shift, x_body, f_body, x_cont, Bind (x_bind, f_cont, f))
)

let red_seq_shift_extend : _ Rewriting2.rule = Rewriting2.(
  seq (shift __ __ __ __ __) __,
  fun is_shift x_body f_body x_cont f_cont f ->
    Shift (is_shift, x_body, f_body, x_cont, Sequence (f_cont, f))
)

(* shift, immediately surronded by reset, is eliminated *)
let red_reset_shift_elim : _ Rewriting2.rule = Rewriting2.(
  reset (shift __ __ __ __ __) __ __,
  fun is_shift x_body f_body x_cont f_cont x_cont' f_cont' ->
    let open Syntax in
    let cont_name = Variables.fresh_variable ~v:"cont" "refined continuation" in
    let cont = term (TLambda (cont_name, [x_cont], Some (Reset (f_cont, x_cont', f_cont')), None)) Lamb in
    let defun = Syntax.(ens ~p:(eq (Variables.res_var ~typ:Lamb) cont) ()) in
    let body = if is_shift then Reset (f_body, x_cont', f_cont') else f_body in
    Bind (x_body, defun, body)
)

(* only on the left, because of req *)
let red_reset_bind : _ Rewriting2.rule = Rewriting2.(
  reset (bind __ __ __) __ __,
  fun b f1 f2 x cont ->
    match f1 with
    | Require _
    | NormalReturn _ -> Bind (b, f1, Reset (f2, x, cont))
    | _ -> Reset (f1, b, compose_cont f2 x cont)
)

(* only on the left, because of req *)
let red_reset_seq : _ Rewriting2.rule = Rewriting2.(
  reset (seq __ __) __ __,
  fun f1 f2 x cont ->
    match f1 with
    | Require _
    | NormalReturn _ -> Sequence (f1, Reset (f2, x, cont))
    | _ -> Reset (f1, (ignored_cont_arg, Any), compose_cont f2 x cont)
)

let red_reset_shift : _ Rewriting2.rule = Rewriting2.(
  reset (shift __ __ __ __ __) __ __,
  fun is_shift x_body f_body x_id f_id x_cont f_cont ->
    let open Syntax in
    let cont_name = Variables.fresh_variable ~v:"cont" "refined continuation" in
    let cont = term (TLambda (cont_name, [x_cont], Some (Reset (f_cont, x_id, f_id)), None)) Lamb in
    let defun = Syntax.(ens ~p:(eq (Variables.res_var ~typ:Lamb) cont) ()) in
    let body = if is_shift then Reset (f_body, x_id, f_id) else f_body in
    (* debug ~at:5 ~title:"red_reset_shift" "cont = %s\nbody = %s" (Pretty.string_of_term cont) (Pretty.string_of_staged_spec body); *)
    Bind (x_body, defun, body)
)

(* only on lhs *)
(* let shift_reset_red_rules : _ Rewriting2.database = [
  red_bind_shift_extend;
  red_seq_shift_extend;
  red_reset_shift_elim;
] *)

let shift_reset_reduce_spec_with (type k)
  (rules : (staged_spec, k) Rewriting2.database) (spec : staged_spec) : staged_spec =
  let@ _ = Hipcore_typed.Globals.Timing.(time norm) in
  let@ _ =
    span (fun r -> debug
      ~at:1
      ~title:"shift_reset_reduction"
      "%s\n==>\n%s"
      (Pretty.string_of_staged_spec spec)
      (string_of_result Pretty.string_of_staged_spec r))
  in
  let spec = Rewriting2.(autorewrite staged rules spec) in
  spec

let shift_reset_reduction_rules_lhs : _ Rewriting2.database = [
  norm_reset_ex;
  norm_reset_disj;
  (* norm_reset_seq_ens; *)
  (* norm_reset_bind_ens; *)
  norm_reset_ens;
  norm_reset_all;
  (* norm_reset_seq_req; *)
  (* norm_reset_bind_req; *)
  (* red_bind_shift_extend;
  red_seq_shift_extend;
  red_reset_shift_elim; *)
  red_reset_seq;
  red_reset_bind;
  red_reset_shift;
]

let shift_reset_reduction_rules_rhs : _ Rewriting2.database = [
]

let shift_reset_reduce_spec_lhs = shift_reset_reduce_spec_with shift_reset_reduction_rules_lhs

let shift_reset_reduce_spec_rhs = shift_reset_reduce_spec_with shift_reset_reduction_rules_rhs
