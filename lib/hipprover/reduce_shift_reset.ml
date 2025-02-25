open Hipcore
open Hiptypes
open Debug
open Pretty
open Subst
open Utilities
open Unfold

exception CannotReduce

let pred_filter pred = not pred.p_rec

(* A hack, we should refactor the code base and make the logic more uniform instead *)
let rec find_continuation_argv (r : string) (cont : spec) : string * spec =
  match cont with
  | NormalReturn (True, EmptyHeap) :: cont' ->
      find_continuation_argv r cont'
  | NormalReturn (Atomic (EQ, Var v1, Var v2), EmptyHeap) :: cont' when v2 = r ->
      v1, cont'
  | _ ->
      r, cont

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
