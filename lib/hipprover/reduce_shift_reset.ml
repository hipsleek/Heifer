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

(* reset (forall x. f) \entails forall x. reset f *)
(* only on the left *)
let norm_reset_all : _ Rewriting2.rule = Rewriting2.(
  reset (forall __ __),
  fun x f -> ForAll (x, Reset f)
)

(* reset (exists x. f) \bientails exists x. reset f *)
(* bientails; both side of the proof *)
let norm_reset_ex : _ Rewriting2.rule = Rewriting2.(
  reset (exists __ __),
  fun x f -> Exists (x, Reset f)
)

(* reset (f1 \/ f2) \bientails reset f1 \/ reset f2 *)
(* bientails; both side of the proof *)
let norm_reset_disj : _ Rewriting2.rule = Rewriting2.(
  reset (disj __ __),
  fun f1 f2 -> Disjunction (Reset f1, Reset f2)
)

(* reset (ens Q; f) \bientails ens Q; reset f *)
(* bientails; both side of the proof *)
let norm_reset_seq_ens : _ Rewriting2.rule = Rewriting2.(
  reset (seq (ens __ __) __),
  fun p k f -> Sequence (NormalReturn (p, k), Reset f)
)

(* reset (req H; f) \entails req H; reset f *)
(* entails; only on the left *)
let norm_reset_seq_req : _ Rewriting2.rule = Rewriting2.(
  reset (seq (req __ __) __),
  fun p k f -> Sequence (Require (p, k), Reset f)
)

let norm_reset_bind_ens : _ Rewriting2.rule = Rewriting2.(
  reset (bind __ (ens __ __) __),
  fun x p k f -> Bind (x, NormalReturn (p, k), Reset f)
)

let norm_reset_bind_req : _ Rewriting2.rule = Rewriting2.(
  reset (bind __ (req __ __) __),
  fun x p k f -> Bind (x, Require (p, k), Reset f)
)

(* reset (ens Q) \bientails ens Q *)
(* both side of the proof *)
let norm_reset_ens : _ Rewriting2.rule = Rewriting2.(
  reset (ens __ __),
  fun p k -> NormalReturn (p, k)
)

(* both sides *)
let shift_reset_normalization_rules_both : _ Rewriting2.database = [
  norm_reset_ex;
  norm_reset_disj;
  norm_reset_seq_ens;
  norm_reset_bind_ens;
  norm_reset_ens;
]

(* lhs only *)
let shift_reset_normalization_rules_lhs_only : _ Rewriting2.database = [
  norm_reset_all;
  norm_reset_seq_req;
  norm_reset_bind_req;
]

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
  reset (shift __ __ __ __ __),
  fun is_shift x_body f_body x_cont f_cont ->
    let open Syntax in
    let cont_name = Variables.fresh_variable ~v:"cont" "refined continuation" in
    let cont = term (TLambda (cont_name, [x_cont], Some (Reset f_cont), None)) Lamb in
    let defun = Syntax.(ens ~p:(eq (Variables.res_var ~typ:Lamb) cont) ()) in
    let body = if is_shift then Reset f_body else f_body in
    Bind (x_body, defun, body)
)

(* only on lhs *)
let shift_reset_red_rules : _ Rewriting2.database = [
  red_bind_shift_extend;
  red_seq_shift_extend;
  red_reset_shift_elim;
]

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
  norm_reset_seq_ens;
  norm_reset_bind_ens;
  norm_reset_ens;
  norm_reset_all;
  norm_reset_seq_req;
  norm_reset_bind_req;
  red_bind_shift_extend;
  red_seq_shift_extend;
  red_reset_shift_elim;
]

let shift_reset_reduction_rules_rhs : _ Rewriting2.database = [
]

let shift_reset_reduce_spec_lhs = shift_reset_reduce_spec_with shift_reset_reduction_rules_lhs

let shift_reset_reduce_spec_rhs = shift_reset_reduce_spec_with shift_reset_reduction_rules_rhs

(* require a small modification to the AST. *)
(* we shall introduce `shift_c`: augment shift with an continuation *)
(* in a nutshell, let's follow the coq version closely *)
