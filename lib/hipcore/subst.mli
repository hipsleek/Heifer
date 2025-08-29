open Hiptypes
open Utils.Hstdlib

type 'a subst_context =
  | Staged : staged_spec subst_context
  | Term : term subst_context
  | Pure : pi subst_context
  | Heap : kappa subst_context

(** Alias for [subst_free_term_vars Staged]. *)
val subst_free_vars : (string * term) list -> staged_spec -> staged_spec

(** Substitute out free variables for a list of terms in a given context.
    (The target locations may not necessarily be terms, e.g. locations in a heap formula.) *)
val subst_free_term_vars : 'a. 'a subst_context -> (string * term) list -> 'a -> 'a

val free_vars : 'a. 'a subst_context -> 'a -> SSet.t
