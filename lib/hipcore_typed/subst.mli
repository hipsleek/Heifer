open Typedhip
open Hipcore.Common

type 'a subst_context =
  | Sctx_staged : staged_spec subst_context
  | Sctx_term : term subst_context
  | Sctx_pure : pi subst_context
  | Sctx_heap : kappa subst_context

(** 1 Substitution-related visitors for specifications *)

(** Alias for [subst_free_term_in Sctx_staged]. *)
val subst_free_vars : (string * term) list -> staged_spec -> staged_spec

(** Alias for [subst_free_term_in Sctx_term]. *)
val subst_free_vars_term : (string * term) list -> term -> term

(** Substitute out free variables for a list of terms in a given context.
    (The target locations may not necessarily be terms, e.g. locations in a heap formula.) *)
val subst_free_vars_in : 'a. 'a subst_context -> (string * term) list -> 'a -> 'a

(** Get all the free variables in a given context. *)
val free_vars : 'a. 'a subst_context -> 'a -> SSet.t

(** Get all the free variables in a given context, and, for free variables
    that appear as term variables, their types. Other free variables (e.g.
    spec binders, names of higher-order stages) are mapped to None. *)
val types_of_free_vars : 'a. 'a subst_context -> 'a -> typ option SMap.t

(** 2 Substitution-related visitors for types *)

val subst_types : 'a. 'a subst_context -> (string * typ) list -> 'a -> 'a

val subst_types_in_type : (string * typ) list -> typ -> typ

val free_type_vars : 'a. 'a subst_context -> 'a -> SSet.t
