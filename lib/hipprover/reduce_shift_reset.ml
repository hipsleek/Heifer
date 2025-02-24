open Hipcore
open Hiptypes
open Debug
open Pretty
open Subst
open Utilities

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
      let e1 : disj_spec = List.concat_map reduce_inside_reset e in
      let e2 : disj_spec = instantiateSpecList ["res", r] e1 in
      let rest1 = reduce_flow rest in
      concatenateSpecsWithSpec e2 rest1
  (* | Shift _ :: _ ->
      failwith "reduce_flow: Shift without Reset" *)
  | e :: rest ->
      concatenateEventWithSpecs [e] (reduce_flow rest)

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
  (* how about reset inside reset? *)
  (* how about higher order inside reset? *)
  match sp with
  | [] -> [[]]
  | Reset (e, r) :: rest ->
      let e1 : disj_spec = List.concat_map reduce_inside_reset e in
      let e2 : disj_spec = instantiateSpecList ["res", r] e1 in
      let rest1 = reduce_inside_reset rest in
      concatenateSpecsWithSpec e2 rest1
  (* | HigherOrder _ :: _ ->
      (* stuck when we see unknown function call *)
      (* unfold if the body contains reset! *)
      failwith "reduce_inside_reset: todo HigherOrder" *)
  | Shift (nz, k, body, r) :: cont ->
      (* let r1 = verifier_getAfreeVar "r" in
      (* reduce the continuation first to know what k is *)
      (* this seems incorrect. What if cont also contains another reset? *)
      (* How about, if cont contains a shift? *)
      let cont1 = reduce_flow [Reset ([cont], Var r1)] in
      (* deep handling/where control/prompt makes a difference *)
      let body1 = List.concat_map (fun (b:spec) ->
          let klamb =
            let p, rest2 =
            (* freshen the parameter of the resulting continuation lambda, as it's already (existentially) bound outside *)
            let p1 = verifier_getAfreeVar "r" in
            (* the return value of shift is assumed to be a variable *)
            let r = retriveFormalArg r in
            p1, instantiateSpecList [r, Var p1] cont1
          in
          TLambda (verifier_getAfreeVar "l", [p; r1], rest2, None)
        in
        debug ~at:2 ~title:"k is?" "%s\n%s" (string_of_disj_spec cont1) (string_of_term klamb);
        let assign = Atomic (EQ, Var k, klamb) in
        (* it seems like we have to keep reducing here *)
        (* List.map *)
        (* let b1 = if nz then [[Reset (b, res_v)]] else b in *)
        (* NormalReturn (assign, EmptyHeap) :: b1 *)
        (* this is where shift0 makes a difference *)
        let b1 = if nz then reduce_flow [Reset ([b], res_v)] else [b] in
        concatenateEventWithSpecs [NormalReturn (assign, EmptyHeap)] b1)
        body
      in
      body1 *)

      (* k is the variable of the continuation *)
      (* cont is restricted by reset? *)
      (* we need to create new cont, by replace the result of shift `r` with a new var *)
      let r = retriveFormalArg r in (* assume to be a variable *)
      let a = verifier_getAfreeVar "a" in
      (* (reset E[(shift k expr)]) => (reset ((lambda (k) expr) (lambda (v) (reset E[v]))))
         The continuation, refined into a lambda, should be wrapped by a reset.
         This is to prevent any further shift in the body of the lambda from
         escaping this delimiter.
       *)
      let lret = verifier_getAfreeVar "lret" in
      (* TODO: we can has empty cont sometimes, try to think about it *)
      let lbody = [[Reset (instantiateSpecList [r, Var a] [cont], Var lret)]] in
      (* cont = \a -> <body> *)
      let lval = TLambda ("<k>", [a; lret], lbody, None) in
      let spec = [Exists [k]; NormalReturn (Atomic (EQ, Var k, lval), EmptyHeap)] in
      let body = concatenateEventWithSpecs spec body in
      (* now we call the body? *)
      (* the body is a disj_spec. Therefore, the result of this reduction
         is a disj_spec *)
      (* the body must be wrapped in reset or not, depending on whether 
         this is a shift0 *)
      let reducer = if nz then reduce_inside_reset else reduce_flow in
      List.concat_map reducer body
  | sp :: rest ->
      concatenateEventWithSpecs [sp] (reduce_inside_reset rest)
