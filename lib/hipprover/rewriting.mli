
open Hipcore
open Hiptypes

(** {1 Unification variables} *)

(** A term which a unification variable may be instantiated with,
  and which may contain encoded unification variables. *)
type uterm =
  | Staged of staged_spec
  | Pure of pi
  | Heap of kappa
  | Term of term
  | Binder of string

val string_of_uterm : uterm -> string

(** A [UF.t] is an efficient unification variable which may be instantiated to a [uterm].
  [UF.t]s are given values by a [UF.store], which is destructively updated on [set]/[union].
  Use [UF.copy] for persistence. *)
module UF :
  sig
    type t
    type store
    val new_store : unit -> store
    val copy : store -> store
    val make : store -> uterm option -> t
    val get : store -> t -> uterm option
    val set : store -> t -> uterm option -> unit
    val eq : store -> t -> t -> bool
    val union : store -> t -> t -> unit
  end

(** {1 Encoded unification variables} *)

(** Defines how unification variables are encoded in a particular structure *)
val is_uvar_name : string -> bool

(** Checks if the topmost constructor of a structure is an encoded unification varibale *)
val get_uvar : uterm -> string option

(** Inject unification variables *)
val uvar_staged : string -> staged_spec
val uvar_heap : string -> kappa
val uvar_pure : string -> pi
val uvar_term : string -> term

(** {1 Unification} *)

(** A unifiable is just a [uterm], but with encoded unification variables replaced by [UF.t]s. *)
type unifiable

val to_unifiable : UF.store -> uterm -> unifiable
val of_unifiable : unifiable -> uterm

val unify : UF.store -> unifiable -> unifiable -> UF.store option

(** {1 Substitution} *)

val subst_uvars : UF.store -> unifiable -> uterm

(** {1 Rewriting} *)

(** A rewrite rule. May contain unification variables (e.g. using [uvar_staged]). *)
type rule

val string_of_rule : rule -> string

(** [rewrite_rooted rule target] rewrites using [rule] at the top level of [target]. *)
val rewrite_rooted : rule -> uterm -> uterm option

(** [rewrite_all rule target] rewrites at all places [rule] may apply in [target]. *)
val rewrite_all : rule -> uterm -> uterm

type database = rule list

val string_of_database : database -> string

(** Rewrites until no more rules in the database apply *)
val autorewrite : database -> uterm -> uterm

(** Combinators for building rules *)
module Rules :
  sig
    module Staged : sig
      val uvar : string -> staged_spec
      val rule : staged_spec -> staged_spec -> rule
      val dynamic_rule : staged_spec -> ((string -> uterm) -> staged_spec) -> rule
      val of_uterm : uterm -> staged_spec
    end

    module Pure : sig
      val uvar : string -> pi
      val rule : pi -> pi -> rule
      val of_uterm : uterm -> pi
    end

    module Heap : sig
      val uvar : string -> kappa
      val rule : kappa -> kappa -> rule
      val of_uterm : uterm -> kappa
    end

    module Term : sig
      val uvar : string -> term
      val rule : term -> term -> rule
      val dynamic_rule : term -> ((string -> uterm) -> term) -> rule
      val of_uterm : uterm -> term
    end

    (** Binders and terms are unrelated, so binders always have to be handled with
      dynamic rules. There are no context patterns or higher-order unification.
      A pattern like (bind x x _) will not unify due to (a dynamic) type mismatch. *)
    module Binder : sig
      val uvar : string -> string
      val of_uterm : uterm -> string
    end
  end
