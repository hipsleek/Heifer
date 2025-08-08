
open Hipcore
open Typedhip
open Common

type map_context = {
  (* list of bound names *)
  mctx_bound: SSet.t;
  (* list of renames needed for capture avoidance.
     these are lazy values so that the new variable name is only generated if needed *)
  mctx_captured_renames: string Lazy.t SMap.t;
}

let add_binder binder mctx = {
  mctx_bound = SSet.add binder mctx.mctx_bound;
  (* remove this from the capture list, since any appearance of the binder is now bound under this name *)
  mctx_captured_renames = SMap.remove binder mctx.mctx_captured_renames;
}

(** In this context, mark that all instances of the variable that would be bound to any
 current binder should be renamed to a fresh variable. *)
let protect_capture mctx = 
  let new_renames = (mctx.mctx_bound 
    |> SSet.to_seq 
    |> Seq.map (fun bound_name -> (bound_name, lazy (Variables.fresh_variable ()))) 
    |> SMap.of_seq) in
  { mctx_captured_renames = SMap.merge_right_priority mctx.mctx_captured_renames new_renames;
    mctx_bound = SSet.empty
  }

let is_bound mctx v = SSet.mem v mctx.mctx_bound
let rename_in_context mctx v =
  match SMap.find_opt v mctx.mctx_captured_renames with
  | Some (lazy v') -> v'
  | None -> v

(** When used to wrap a function, will automatically rename free variables in this node
 that would be captured by a binder in the current scope. *)
let with_capture_avoidance f (bind_ctx, env) = f (protect_capture bind_ctx, env)

(** 
  A binder-aware AST map visitor.

  The environment type of this visitor is [map_context * 'a], where ['a] is inferred based on the subclass,
  and is analogous to the environment type of the original visitor [map_spec].
  
  When overriding a method, call the appropriate method of the superclass (i.e. this class)
  during the traversal. This is so proper tracking of binders can be maintained.
  
  Further, be careful of the possiblity of infinite loops.
 *)
class ['self] map_spec_with_binders = object (self)
  inherit ['self] map_spec as super
  
  (* AST nodes that can create free variables. these need to be checked against the captured renames *)

  method! visit_Var (bind_ctx, _) v = Var (rename_in_context bind_ctx v)

  (* AST nodes that create binders. these need to be added to the context *)

  method! visit_Exists (bind_ctx, env) x f =
    super#visit_Exists (add_binder (ident_of_binder x) bind_ctx, env) x f

  method! visit_ForAll (bind_ctx, env) x f =
    super#visit_ForAll (add_binder (ident_of_binder x) bind_ctx, env) x f

  method! visit_Bind (bind_ctx, env) x f1 f2 =
    let f1 = super#visit_staged_spec (bind_ctx, env) f1 in
    let f2 = super#visit_staged_spec (add_binder x bind_ctx, env) f2 in
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
    let body = super#visit_staged_spec (add_binder k bind_ctx, env) body in
    let cont = super#visit_staged_spec (add_binder (ident_of_binder x) bind_ctx, env) cont in
    Shift (nz, k, body, x, cont)

  (* TODO We also need to override visit_term_desc, visit_staged_spec, etc...
     so that when the subclass calls their respective parent methods, the call is dispatched
     into our binder-aware methods instead of potentially calling the child class again,
     causing an infinite loop. *)

  method! visit_term_desc (bind_ctx, env) td =
    match td with
    | Var v -> self#visit_Var (bind_ctx, env) v
    | _ -> super#visit_term_desc (bind_ctx, env) td

end

(** Create an empty binder context, and use it to call a visitor function. *)
let visit_using_env f env =
  let empty_map_context = {
    mctx_bound = SSet.empty;
    mctx_captured_renames = SMap.empty;
  } in
  f (empty_map_context, env)
