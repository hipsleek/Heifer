open Typedhip

(** Holder of contextual information during an AST traversal. *)
type map_context

(** 
  A binder-aware AST map visitor.

  The environment type of this visitor is [map_context * 'a], where ['a] is inferred based on the subclass,
  and is analogous to the environment type of the original visitor [map_spec].
  
  When overriding a method, call the appropriate method of the superclass (i.e. this class)
  during the traversal. This is so proper tracking of binders can be maintained.
 *)
class ['self] map_spec_with_binders : object
  inherit ['self] map_spec

  (* we write down the signature of one method, to get the type checker to unify
     map_spec's 'env type with our own map_context * 'env type *)
  method visit_staged_spec : 'monomorphic. map_context * 'env -> staged_spec -> staged_spec
end

(** Check if a variable is bound in the current context. *)
val is_bound : map_context -> string -> bool

(** Create an empty context, and use it to call a visitor function. *)
val visit_using_env : (map_context * 'env -> 'visitor) -> 'env -> 'visitor
