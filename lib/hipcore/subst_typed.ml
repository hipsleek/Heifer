open Typedhip

(* replaces free variables *)
let subst_free_vars_term (substitutions : (string * term) list) term =
  let subst_visitor = object
    inherit [_] map_spec as super
    
    method! visit_term env t =
      match t.term_desc with
      | Var v -> begin
        match List.assoc_opt v substitutions with
        | Some sub -> sub
        | None -> t
      end
      | _ -> super#visit_term env t
  end
  in
  subst_visitor#visit_term () term
