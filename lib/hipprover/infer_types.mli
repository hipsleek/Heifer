open Hipcore.Types
open Hipcore_typed
open Typedhip
open Utils

(** {1 Typing context} *)

(** A typing context is a [Types.abs_typ_env] wrapped in the State monad. *)
type 'a using_env = ('a, abs_typ_env) State.state

val (let*) : 'a using_env -> ('a -> 'b using_env) -> 'b using_env 
val return : 'a -> 'a using_env

(** Exception raised when solver cannot unify the two types. *)
exception Unification_failure of typ * typ

(** [Cyclic_type t1 t2] is raised when, during type unification, t1's value
    is found to rely on t2. *)
exception Cyclic_type of typ * typ

(** {1 Inference primitives} *)

(** Record a (nontrivial) equality in the typing environment. *)
val unify_types : typ -> typ -> unit using_env

(** Record the type (or constraints on) of a program variable in the typing environment. *)
val assert_var_has_type : binder -> typ -> unit using_env

(** {1 Context managers} *)

(** Run a typing computation using an empty context. *)
val with_empty_env : 'a using_env -> ('a * abs_typ_env)

(** Add a sequence of bindings to the given typing computation. The bindings' scope
    is tied to the computation, and will be cleared on exit. *)
val with_vartypes : binder Seq.t -> 'a using_env -> 'a using_env

(** {1 Type simplifiers}
  Type equalities are not immediately updated in the AST after they are discovered
  using unification. This is handled by a final type simplification pass that occurs after
  traversal. The [infer_types] functions already run this pass within their own inputs;
  but when manually threading together type computations in multiple nodes,
  this must be done manually. *)

val simplify_types_pi : pi -> pi using_env
val simplify_types_staged_spec : staged_spec -> staged_spec using_env
val simplify_types_core_lang : core_lang -> core_lang using_env

(** {1 Type inferrers}
  The main entry points to the inference mechanism. [with_vartypes] can be used
  to add some initial bindings to the context. *)

val infer_types_core_lang : core_lang -> core_lang using_env
val infer_types_staged_spec : staged_spec -> staged_spec using_env
val infer_types_term : ?hint : typ -> term -> term using_env
val infer_types_pi : pi -> pi using_env
val infer_types_state : state -> state using_env
val infer_types_kappa : kappa -> kappa using_env
val infer_types_pair_pi : pi -> pi -> (pi * pi) using_env
val infer_types_pair_staged_spec : staged_spec -> staged_spec -> (staged_spec * staged_spec) using_env

