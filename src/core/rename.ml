open Bindlib
open Names

module Core : Renaming = struct
  type ctxt = Fresh.t

  let empty_ctxt = Fresh.empty
  let reset_context_for_closed_terms = false
  let skip_constant_binders = false
  let constant_binder_name = None
  let new_name = Fresh.fresh
  let reserve_name = Fresh.add
  let remove_name = Fresh.remove
end

include Ctxt (Core)
