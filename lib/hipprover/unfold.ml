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
   | HigherOrder ((name, args), ret) :: s1
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
                (fun disj -> p1 |> Acc.add_all disj)
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

(** Gets the predicate definition of the first higher-order stage in the spec,
    that satisfies the given filtering condition.
  *)
let get_first_predicate_spec
  (filter : pred_def -> bool)
  (predicates : pred_def SMap.t)
  (sp : spec) : pred_def option =
  let f = function
    | HigherOrder ((name, _), _) ->
        let pred_opt = SMap.find_opt name predicates in
        let bind_opt pred = if filter pred then Some pred else None in
        Option.bind pred_opt bind_opt
    | _ ->
        None
  in
  List.find_map f sp

let try_unfold_first_predicate_spec
  (filter : pred_def -> bool)
  (predicates : pred_def SMap.t)
  (sp : spec) : disj_spec =
  match get_first_predicate_spec filter predicates sp with
  | None ->
      [sp]
  | Some pred ->
      unfold_predicate_spec "try_unfold_first_predicate_spec" pred sp

let rec recursively_unfold_predicates_spec
  (filter : pred_def -> bool)
  (predicates : pred_def SMap.t)
  (sp : spec) : disj_spec =
  match get_first_predicate_spec filter predicates sp with
  | None ->
      [sp]
  | Some pred ->
      let dsp = unfold_predicate_spec "try_unfold_first_predicate_spec" pred sp in
      recursively_unfold_predicates_disj_spec filter predicates dsp

and recursively_unfold_predicates_disj_spec
  (filter : pred_def -> bool)
  (predicates : pred_def SMap.t)
  (dsp : disj_spec) =
  List.concat_map (recursively_unfold_predicates_spec filter predicates) dsp
