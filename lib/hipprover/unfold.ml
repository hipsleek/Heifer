open Hipcore
open Hiptypes
open Pretty
open Normalize
open Debug

let rename_exists_pred (pred : pred_def) : pred_def =
  { pred with p_body = Forward_rules.renamingexistientalVar pred.p_body }

let instantiate_pred : pred_def -> term list -> term -> pred_def =
  fun pred args ret ->
   let@ _ =
     Debug.span (fun r ->
         debug ~at:4 ~title:"instantiate_pred" "%s\n%s\n%s\n==> %s"
           (string_of_pred pred)
           (string_of_list string_of_term args)
           (string_of_term ret)
           (string_of_result string_of_pred r))
   in
   (* the predicate should have one more arg than arguments given for the return value, which we'll substitute with the return term from the caller *)
   (* Format.printf "right before instantiate %s@." (string_of_pred pred); *)
   let pred = rename_exists_pred pred in
   (* Format.printf "rename exists %s@." (string_of_pred pred); *)
   let params, ret_param = unsnoc pred.p_params in
   let bs = (ret_param, ret) :: bindFormalNActual (*List.map2 (fun a b -> (a, b)) *) params args in
   let p_body =
     let bbody =
       pred.p_body |> List.map (fun b -> List.map (Subst.instantiateStages bs) b)
     in
     (* Format.printf "bs %s@."
          (string_of_list (string_of_pair Fun.id string_of_term) bs);
        Format.printf "pred.p_body %s@." (string_of_disj_spec pred.p_body);
        Format.printf "bbody %s@."
          (string_of_list (string_of_list string_of_staged_spec) bbody); *)
     bbody
   in
   { pred with p_body }

 let rec unfold_predicate_aux pred prefix (s : spec) : disj_spec =
   match s with
   | [] ->
     let r = List.map Acc.to_list prefix in
     r
   | HigherOrder (p, h, (name, args), ret) :: s1
     when String.equal name pred.p_name ->
     (* debug ~at:1
        ~title:(Format.asprintf "unfolding: %s" name)
        "%s" (string_of_pred pred); *)
     let pred1 = instantiate_pred pred args ret in
     (* debug ~at:1
        ~title:(Format.asprintf "instantiated: %s" name)
        "%s" (string_of_pred pred1); *)
     let prefix =
       prefix
       |> List.concat_map (fun p1 ->
              List.map
                (fun disj ->
                  p1 |> Acc.add (NormalReturn (p, h)) |> Acc.add_all disj)
                pred1.p_body)
     in
     unfold_predicate_aux pred prefix s1
   | c :: s1 ->
     let pref = List.map (fun p -> Acc.add c p) prefix in
     unfold_predicate_aux pred pref s1

 (* let unfold_predicate : pred_def -> disj_spec -> disj_spec =
    fun pred ds ->
     List.concat_map (fun s -> unfold_predicate_aux pred [Acc.empty] s) ds *)

 (** f;a;e \/ b and a == c \/ d
   => f;(c \/ d);e \/ b
   => f;c;e \/ f;d;e \/ b *)
 let unfold_predicate_spec : string -> pred_def -> spec -> disj_spec =
  fun which pred sp ->
   let@ _ =
     Debug.span (fun r ->
         debug ~at:1
           ~title:(Format.asprintf "unfolding (%s): %s" which pred.p_name)
           "%s\nin\n%s\n==>\n%s" (string_of_pred pred) (string_of_spec sp)
           (string_of_result string_of_disj_spec r))
   in
   unfold_predicate_aux pred [Acc.empty] sp

let unfold_predicate_norm
  (which : string)
  (pred : pred_def)
  (sp : normalisedStagedSpec) : normalisedStagedSpec list =
  List.map normalize_spec
    (unfold_predicate_spec which pred (normalisedStagedSpec2Spec sp))

let try_unfold_predicates_spec
  (predicates : pred_def SMap.t)
  (sp : spec) : disj_spec =
  let extract_name1 = function
    | HigherOrder (_, _, (name, _), _) -> Some name
    | _ -> None
  in
  let extract_names sp = List.filter_map extract_name1 sp in
  let try_unfold1 name sp : disj_spec =
    try
      let pred = SMap.find name predicates in
      if pred.p_rec then [sp] else unfold_predicate_spec "try_unfold_predicates" pred sp
    with
      Not_found -> [sp]
  in
  let try_unfolds sp : disj_spec =
    let names = extract_names sp in
    let step dsp name = List.concat_map (try_unfold1 name) dsp in
    List.fold_left step [sp] names
  in
  try_unfolds sp
  (* List.concat_map try_unfold_predicate names *)
  (* repeat more, think! *)

let try_unfold_predicates_disj_spec (predicates : pred_def SMap.t) (dsp : disj_spec) =
  List.concat_map (try_unfold_predicates_spec predicates) dsp
