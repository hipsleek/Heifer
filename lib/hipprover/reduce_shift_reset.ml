open Hipcore
open Hiptypes
open Debug
open Pretty
open Subst
open Utilities
open Unfold

let rec shift_reset_reduction (dsp : disj_spec) : disj_spec =
  let@ _ =
    Debug.span
      (fun r -> debug
        ~at:2
        ~title:"shift_reset_reduction"
        "%s\n==>\n%s"
        (string_of_disj_spec dsp)
        (string_of_result string_of_disj_spec r))
  in
  List.concat_map reduce_flow dsp

and reduce_flow (sp : spec) : disj_spec =
  let@ _ =
    Debug.span
      (fun r -> debug
        ~at:2
        ~title:"reduce_flow"
        "%s\n==>\n%s"
        (string_of_spec sp)
        (string_of_result string_of_disj_spec r))
  in
  match sp with
  | [] -> [[]]
  | Reset (e, r) :: rest ->
      let e' = reduce_reset e r in
      let rest1 = reduce_flow rest in
      concatenateSpecsWithSpec e' rest1
  (* | Shift _ :: _ ->
      failwith "reduce_flow: Shift without Reset" *)
  | e :: rest ->
      concatenateEventWithSpecs [e] (reduce_flow rest)

and reduce_inside_reset_aux (sp : spec) : disj_spec =
  (* how about reset inside reset? *)
  (* how about higher order inside reset? *)
  match sp with
  | [] -> [[]]
  | Reset (e, r) :: rest ->
      let e' = reduce_reset e r in
      let rest1 = reduce_inside_reset_aux rest in
      concatenateSpecsWithSpec e' rest1
  | Shift (_nz, k, body, r) :: cont ->
      (* k is the variable of the continuation *)
      (* we need to create new cont, by replace the result of shift `r` with a new var *)
      let r = retriveFormalArg r in (* assume to be a variable *)
      let a = verifier_getAfreeVar "a" in
      (* (reset E[(shift k expr)]) => (reset ((lambda (k) expr) (lambda (v) (reset E[v]))))
         The continuation, refined into a lambda, should be wrapped by a reset.
         This is to prevent any further shift in the body of the lambda from
         escaping this delimiter.
       *)
      let lret = verifier_getAfreeVar "lret" in
      let cont_sp = match cont with
        | [] -> [NormalReturn (res_eq (Var a), EmptyHeap)]
        | _ -> instantiateSpec [r, Var a] cont
      in
      (* let lbody = [[Reset ([cont_sp], Var lret)]] in *)
      let lbody = reduce_flow [Reset ([cont_sp], Var lret)] in
      (* cont = \a -> <body> *)
      let lval = TLambda ("<k>", [a; lret], lbody, None) in
      let spec = [Exists [k]; NormalReturn (Atomic (EQ, Var k, lval), EmptyHeap)] in
      let body = concatenateEventWithSpecs spec body in
      (* now we call the body? *)
      (* the body is a disj_spec. Therefore, the result of this reduction
         is a disj_spec *)
      (* the body must be wrapped in reset or not, depending on whether
         this is a shift0 *)
      (* let reducer = if nz then reduce_inside_reset_aux else reduce_flow in *)
      List.concat_map reduce_inside_reset_aux body
  | sp :: rest ->
      concatenateEventWithSpecs [sp] (reduce_inside_reset_aux rest)

and reduce_inside_reset (sp : spec) : disj_spec =
  let@ _ =
    Debug.span
      (fun r -> debug
        ~at:2
        ~title:"reduce_inside_reset"
        "%s\n==>\n%s"
        (string_of_spec sp)
        (string_of_result string_of_disj_spec r))
  in
  match try_unfold_all sp with
  | None -> [sp]
  | Some dsp -> List.concat_map reduce_inside_reset_aux dsp

and reduce_reset (e : disj_spec) (r : term) : disj_spec =
  let e1 = List.concat_map reduce_inside_reset e in
  let e2 = instantiateSpecList ["res", r] e1 in
  e2
