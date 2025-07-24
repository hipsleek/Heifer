open Typedhip
open Syntax
open Rewrite_context

(* TODO is it possible to instead use an API that doesn't mix term substitutions with
   heap location/HOF substitutions? *)

let find_term_binding ~typ x bindings =
  match List.assoc_opt x bindings with
  | None -> term (Var x) typ
  | Some t -> t

let find_non_term_binding x bindings =
  match List.assoc_opt x bindings with
  | Some {term_desc = Var name; _} -> name
  | _ -> x

let subst_visitor = object
  inherit [_] map_spec_with_binders as super

  method! visit_Var (env, bindings) v =
    let new_desc =
      match List.assoc_opt v bindings with
      | Some t when not (is_bound env v) -> t.term_desc
      | _ -> Var v
    in
    with_capture_avoidance super#visit_term_desc (env, bindings) new_desc

  method! visit_PointsTo (env, bindings) loc value =
    let new_name = find_non_term_binding loc bindings in
    super#visit_PointsTo (env, bindings) new_name value

  method! visit_HigherOrder (env, bindings) f args =
    let new_name = find_non_term_binding f bindings in
    super#visit_HigherOrder (env, bindings) new_name args
end

let subst_free_vars bindings ctx =
  visit_using_env subst_visitor#visit_staged_spec bindings ctx

let subst_free_vars_term bindings ctx =
  visit_using_env subst_visitor#visit_term bindings ctx


(* let subst_free_vars bs ctx = *)
(*   let subst_visitor free = *)
(*     object (self) *)
(*       inherit [_] map_spec as super *)
(**)
(*       (* most of the work done by this visitor is done here *) *)
(*       method! visit_term bindings t = *)
(*         match t.term_desc with *)
(*         | Var v -> find_term_binding ~typ:t.term_type v bindings *)
(*         | _ -> super#visit_term bindings t *)
(**)
(*       (* a few other constructs contain implicit variables *) *)
(*       method! visit_HigherOrder bindings f v = *)
(*         let v1 = self#visit_list self#visit_term bindings v in *)
(*         let f1 = find_non_term_binding f bindings in *)
(*         HigherOrder (f1, v1) *)
(**)
(*       method! visit_PointsTo bindings x v = *)
(*         let v1 = self#visit_term bindings v in *)
(*         let f1 = find_non_term_binding x bindings in *)
(*         PointsTo (f1, v1) *)
(**)
(*       (* the remaining cases handle capture-avoidance in binders *) *)
(*       method! visit_Shift bindings nz k body x cont = *)
(*         let k1, body1 = *)
(*           if SSet.mem k free then *)
(*             let y = Variables.fresh_variable ~v:k () in *)
(*             (y, self#visit_staged_spec [(k, Var y)] body) *)
(*           else *)
(*             (k, body) *)
(*         in *)
(*         let x1, cont1 = *)
(*           if SSet.mem x free then *)
(*             let y = Variables.fresh_variable ~v:x () in *)
(*             (y, self#visit_staged_spec [(x, Var y)] body) *)
(*           else *)
(*             (x, cont) *)
(*         in *)
(*         let bs_k = List.filter (fun (b, _) -> b <> k1) bindings in *)
(*         let bs_x = List.filter (fun (b, _) -> b <> x1) bindings in *)
(*         Shift (nz, k1, self#visit_staged_spec bs_k body1, x1, self#visit_staged_spec bs_x cont1) *)
(**)
(*       method! visit_Exists bindings x f = *)
(*         let x1, f1 = *)
(*           if SSet.mem x free then *)
(*             let y = Variables.fresh_variable ~v:x () in *)
(*             (y, self#visit_staged_spec [(x, Var y)] f) *)
(*           else (x, f) *)
(*         in *)
(*         let bs = List.filter (fun (b, _) -> b <> x1) bindings in *)
(*         Exists (x1, self#visit_staged_spec bs f1) *)
(**)
(*       method! visit_ForAll bindings x f = *)
(*         let x1, f1 = *)
(*           if SSet.mem x free then *)
(*             let y = Variables.fresh_variable ~v:x () in *)
(*             (y, self#visit_staged_spec [(x, Var y)] f) *)
(*           else (x, f) *)
(*         in *)
(*         let bs = List.filter (fun (b, _) -> b <> x1) bindings in *)
(*         ForAll (x1, self#visit_staged_spec bs f1) *)
(**)
(*       method! visit_Bind bindings x f1 f2 = *)
(*         let x1, f2 = *)
(*           if SSet.mem x free then *)
(*             let y = Variables.fresh_variable ~v:x () in *)
(*             (y, self#visit_staged_spec [(x, Var y)] f2) *)
(*           else (x, f2) *)
(*         in *)
(*         let bs = List.filter (fun (b, _) -> b <> x1) bindings in *)
(*         Bind (x1, self#visit_staged_spec bs f1, self#visit_staged_spec bs f2) *)
(**)
(*       method! visit_TLambda bindings name params sp body = *)
(*         let params1, sp1, body1 = *)
(*           List.fold_right *)
(*             (fun p (ps, sp, body) -> *)
(*               if SSet.mem p free then *)
(*                 let y = Variables.fresh_variable ~v:p () in *)
(*                 ( p :: ps, *)
(*                   self#visit_option self#visit_staged_spec [(p, Var y)] sp, *)
(*                   self#visit_option self#visit_core_lang [(p, Var y)] body ) *)
(*               else (p :: ps, sp, body)) *)
(*             params ([], sp, body) *)
(*         in *)
(*         let bs = *)
(*           List.filter (fun (b, _) -> not (List.mem b params1)) bindings *)
(*         in *)
(*         TLambda *)
(*           ( name, *)
(*             params1, *)
(*             self#visit_option self#visit_staged_spec bs sp1, *)
(*             self#visit_option self#visit_core_lang bs body1 ) *)
(**)
(*       method! visit_CLambda bindings params sp body = *)
(*         let params1, sp1, body1 = *)
(*           List.fold_right *)
(*             (fun p (ps, sp, body) -> *)
(*               if SSet.mem p free then *)
(*                 let y = Variables.fresh_variable ~v:p () in *)
(*                 ( p :: ps, *)
(*                   self#visit_option self#visit_staged_spec [(p, Var y)] sp, *)
(*                   self#visit_core_lang [(p, Var y)] body ) *)
(*               else (p :: ps, sp, body)) *)
(*             params ([], sp, body) *)
(*         in *)
(*         let bs = *)
(*           List.filter (fun (b, _) -> not (List.mem b params1)) bindings *)
(*         in *)
(*         CLambda *)
(*           ( params1, *)
(*             self#visit_option self#visit_staged_spec bs sp1, *)
(*             self#visit_core_lang bs body1 ) *)
(*     end *)
(*   in *)
(*   let free = List.map snd bs |> List.map (free_vars Term) |> SSet.concat in *)
(*   (subst_visitor free)#visit_staged_spec bs ctx *)
