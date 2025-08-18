
open Hipcore
open Typedhip
open Common

type map_context = {
  (* list of bound names *)
  mctx_bound: SSet.t;
}

let add_binder binder mctx = {
  mctx_bound = SSet.add binder mctx.mctx_bound;
}

let is_bound mctx v = SSet.mem v mctx.mctx_bound

class ['self] map_spec_with_binders = object
  inherit ['self] map_spec as super
  
  (* AST nodes that create binders. these need to be added to the context *)

  method! visit_Exists (bind_ctx, env) x f =
    super#visit_Exists (add_binder (ident_of_binder x) bind_ctx, env) x f

  method! visit_ForAll (bind_ctx, env) x f =
    super#visit_ForAll (add_binder (ident_of_binder x) bind_ctx, env) x f

  method! visit_Bind (bind_ctx, env) x f1 f2 =
    let f1 = super#visit_staged_spec (bind_ctx, env) f1 in
    let f2 = super#visit_staged_spec (add_binder (ident_of_binder x) bind_ctx, env) f2 in
    Bind (x, f1, f2)

  method! visit_TLambda (bind_ctx, env) name params spec body =
    let new_bind_ctx = List.fold_right add_binder (List.map ident_of_binder params) bind_ctx in
    let spec = Option.map (super#visit_staged_spec (new_bind_ctx, env)) spec in
    let body = Option.map (super#visit_core_lang (new_bind_ctx, env)) body in
    TLambda (name, params, spec, body)

  method! visit_CLambda (bind_ctx, env) params spec body =
    let new_bind_ctx = List.fold_right add_binder (List.map ident_of_binder params) bind_ctx in
    let spec = Option.map (super#visit_staged_spec (new_bind_ctx, env)) spec in
    let body = super#visit_core_lang (new_bind_ctx, env) body in
    CLambda (params, spec, body)

  method! visit_Shift (bind_ctx, env) nz k body x cont =
    let body = super#visit_staged_spec (add_binder (ident_of_binder k) bind_ctx, env) body in
    let cont = super#visit_staged_spec (add_binder (ident_of_binder x) bind_ctx, env) cont in
    Shift (nz, k, body, x, cont)

end

let visit_using_env f env =
  let empty_map_context = {
    mctx_bound = SSet.empty;
  } in
  f (empty_map_context, env)
