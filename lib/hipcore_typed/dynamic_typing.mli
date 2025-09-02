open Typedhip

(** Enable dynamic typing. This disables all type checks before translation to SMT.
    This does not do anything by itself; relevant areas of the library whose
    behaviors differ between untyped and typed mode must check this flag
    using [dynamic_typing_enabled].

    This must be called before any input is processed. *)
val set_dynamic_typing : unit -> unit

val dynamic_typing_enabled : unit -> bool

(** Replace all types in this specification with [Any]. *)
val type_with_any_spec : staged_spec -> staged_spec

(** Replace all [Any] types in this pure formula with fresh type variables.
    Inferring these types can be done using one of the [Infer_types] endpoints. *)
val instantiate_any_types_pi : pi -> pi

(* Currently, the only untyped extensions are shift/reset. *)

val uses_untyped_extensions_spec : staged_spec -> bool
val uses_untyped_extensions_core : core_lang -> bool
