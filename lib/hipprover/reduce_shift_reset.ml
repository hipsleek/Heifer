open Hipcore
open Hiptypes

let rec shift_reset_reduction (dsp:disj_spec) : disj_spec =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:2
          ~title:"shift_reset_reduction"
          "%s\n==>\n%s" (string_of_disj_spec dsp)
          (string_of_result string_of_disj_spec r))
  in
  List.concat_map reduce_flow dsp

and reduce_flow (sp:spec) : disj_spec =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:2
          ~title:"reduce_flow"
          "%s\n==>\n%s" (string_of_spec sp)
          (string_of_result string_of_disj_spec r))
  in
  match sp with
  | [] -> [[]]
  | Reset (e, r) :: rest ->
    let e1 = List.concat_map reduce_inside_reset e in
    let e2 = instantiateSpecList ["res", r] e1 in
    let rest1 = reduce_flow rest in
    concatenateSpecsWithSpec e2 rest1
  | e :: rest -> concatenateEventWithSpecs [e] (reduce_flow rest)

and reduce_inside_reset (sp:spec) : disj_spec =
  let@ _ =
    Debug.span (fun r ->
        debug ~at:2
          ~title:"reduce_inside_reset"
          "%s\n==>\n%s" (string_of_spec sp)
          (string_of_result string_of_disj_spec r))
  in
  match sp with
  | [] -> [[]]
  | Shift (nz, k, body, r) :: cont ->
    let r1 = verifier_getAfreeVar "r" in
    (* reduce the continuation first to know what k is *)
    let cont1 =
      (* deep handling/where control/prompt makes a difference *)
      reduce_flow [Reset ([cont], Var r1)]
    in
    let body1 = body |> List.concat_map (fun (b:spec) ->
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
    in
    body1
  | sp :: rest ->
    concatenateEventWithSpecs [sp] (reduce_inside_reset rest)