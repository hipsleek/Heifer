open Typedhip

let status = ref false

let set_dynamic_typing () = status := true

let dynamic_typing_enabled () = !status

let spec_visitor f = object
  inherit [_] map_spec

  method! visit_typ _ t = f t
end

let type_with_any_spec s = (spec_visitor (fun _ -> Any))#visit_staged_spec () s

let instantiate_any_types_pi p = (spec_visitor (fun _ -> TVar (Variables.fresh_variable ())))#visit_pi () p

let check_for_untyped_visitor = object
  inherit [_] reduce_spec

  method zero = false
  method plus = (||)

  method! visit_CShift _ _ _ _ = true
  method! visit_CReset _ _ = true

  method! visit_Shift _ _ _ _ _ _ = true
  method! visit_Reset _ _ = true
end

let uses_untyped_extensions_spec s = check_for_untyped_visitor#visit_staged_spec () s

let uses_untyped_extensions_core c = check_for_untyped_visitor#visit_core_lang () c
