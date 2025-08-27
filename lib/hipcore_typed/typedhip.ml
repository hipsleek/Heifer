
include Typed_core_ast

let var_of_binder (v, t) = {term_desc = Var v; term_type = t}
let binder_of_var {term_desc; term_type} =
  match term_desc with
  | Var v -> (v, term_type)
  | _ -> raise (Invalid_argument "Term was not Var")
let ident_of_binder ((v, _) : binder) = v
let type_of_binder ((_, t) : binder) = t


type tactic = Hipcore_common.Tactics.tactic

include Hipcore_common.Data.Make(Typed_core_ast)

type 'a quantified = binder list * 'a

