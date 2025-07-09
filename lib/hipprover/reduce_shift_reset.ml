open Hipcore
open Hiptypes
open Debug
(*
open Pretty
open Subst
*)

open Utils

(*
exception CannotReduce

let pred_filter pred = not pred.p_rec
*)

(*
(* A hack, we should refactor the code base and make the logic more uniform instead *)
let rec find_continuation_argv (r : string) (cont : spec) : string * spec =
  match cont with
  | NormalReturn (True, EmptyHeap) :: cont' ->
      find_continuation_argv r cont'
  | NormalReturn (Atomic (EQ, Var v1, Var v2), EmptyHeap) :: cont' when v2 = r ->
      v1, cont'
  | _ ->
      r, cont
*)

(*
let rec shift_reset_reduction (predicates : pred_def SMap.t) (dsp : disj_spec) : disj_spec =
  let@ _ =
    Debug.span
      (fun r -> debug
        ~at:2
        ~title:"shift_reset_reduction"
        "%s\n==>\n%s"
        (string_of_disj_spec dsp)
        (string_of_result string_of_disj_spec r))
  in
  reduce_flow predicates dsp

and reduce_flow (predicates : pred_def SMap.t) (dsp : disj_spec) : disj_spec =
  let@ _ =
    Debug.span
      (fun r -> debug
        ~at:2
        ~title:"reduce_flow"
        "%s\n==>\n%s"
        (string_of_disj_spec dsp)
        (string_of_result string_of_disj_spec r))
  in
  debug ~at:5 ~title:"available predicates" "%s" (String.concat ", " (SMap.keys predicates));
  let dsp = recursively_unfold_predicates_disj_spec pred_filter predicates dsp in
  let dsp = List.concat_map (reduce_inside_flow predicates) dsp in
  dsp

and reduce_inside_flow (predicates : pred_def SMap.t) (sp : spec) : disj_spec =
  debug ~at:5 ~title:"reduce inside flow" "%s" (string_of_spec sp);
  match sp with
  | [] -> [[]]
  | Reset (e, r) :: rest ->
      let e' = reduce_reset predicates e r in
      let rest1 = reduce_inside_flow predicates rest in
      concatenateSpecsWithSpec e' rest1
  | e :: rest ->
      concatenateEventWithSpecs [e] (reduce_inside_flow predicates rest)

and reduce_inside_reset (predicates : pred_def SMap.t) (sp : spec) : disj_spec =
  debug ~at:5 ~title:"reduce inside reset" "%s" (string_of_spec sp);
  match sp with
  | [] -> [[]]
  | Reset (e, r) :: rest ->
      let e' = reduce_reset predicates e r in
      let rest1 = reduce_inside_reset predicates rest in
      concatenateSpecsWithSpec e' rest1
  | HigherOrder ((name, _args), _term) :: _ ->
      debug
        ~at:5
        ~title:"HigherOrder during shift/reset reduction"
        "%s" name;
      (* expand the predicate here. If we cannot expand the predicate, throws? *)
      (* concatenateEventWithSpecs [stage] (reduce_inside_reset predicates rest) *)
      raise CannotReduce
  | Shift (_nz, k, body, r) :: cont ->
      (* k is the variable of the continuation *)
      let fresh_k = verifier_getAfreeVar k ^ "_" ^ k in
      let body = instantiateSpecList [k, Var fresh_k] body in
      let r = retriveFormalArg r in (* assume to be a variable *)
      let r, cont = find_continuation_argv r cont in (* a hack here! *)
      debug ~at:5 ~title:"continuation argv" "%s" r;
      let a = verifier_getAfreeVar "a" in
      let lret = verifier_getAfreeVar "lret" in
      let cont_sp = match cont with
        | [] -> [NormalReturn (res_eq (Var a), EmptyHeap)]
        | _ -> instantiateSpec [r, Var a] cont
      in
      (* (reset E[(shift k expr)]) => (reset ((lambda (k) expr) (lambda (v) (reset E[v]))))
         The continuation, refined into a lambda, should be wrapped by a reset.
         This is to prevent any further shift in the body of the lambda from
         escaping this delimiter.
       *)
      (* let lbody = [[Reset ([cont_sp], Var lret)]] in *)
      let lbody = reduce_inside_flow predicates [Reset ([cont_sp], Var lret)] in
      (* cont = \a -> <body> *)
      let lparams = [a; lret] in
      let lval = TLambda (fresh_k, lparams, lbody, None) in
      let spec = [Exists [fresh_k]; NormalReturn (Atomic (EQ, Var fresh_k, lval), EmptyHeap)] in
      let body = concatenateEventWithSpecs spec body in
      let lpred = { p_name = fresh_k; p_params = lparams; p_rec = false; p_body = lbody } in
      let updated_predicates = SMap.add fresh_k lpred predicates in
      (* now we call the body? *)
      (* the body must be wrapped in reset or not, depending on whether
         this is a shift0 *)
      (* let reducer = if nz then reduce_inside_reset_aux else reduce_inside_flow in *)
      reduce_inside_flow updated_predicates [Reset (body, res_v)]
  | stage :: rest ->
      concatenateEventWithSpecs [stage] (reduce_inside_reset predicates rest)

and reduce_reset (predicates : pred_def SMap.t) (dsp : disj_spec) (res : term) : disj_spec =
  let@ _ =
    Debug.span
      (fun r -> debug
        ~at:2
        ~title:"reduce_reset"
        "%s\n==>\n%s"
        (string_of_disj_spec dsp)
        (string_of_result string_of_disj_spec r))
  in
  let reduce_spec sp =
    try
      reduce_inside_reset predicates sp
    with CannotReduce ->
      [[Reset ([sp], res)]]
  in
  debug ~at:5 ~title:"available predicates" "%s" (String.concat ", " (SMap.keys predicates));
  let dsp = recursively_unfold_predicates_disj_spec pred_filter predicates dsp in
  let dsp = List.concat_map reduce_spec dsp in
  let dsp = instantiateSpecList ["res", res] dsp in
  dsp
*)

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
    let cont_name = Variables.fresh_variable ~v:"cont" "refined continuation" in
    let cont = TLambda (cont_name, [x_cont], Some (Reset f_cont), None) in
    let defun = Syntax.(ens ~p:(eq Variables.res_var cont) ()) in
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
  let@ _ = Globals.Timing.(time norm) in
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
