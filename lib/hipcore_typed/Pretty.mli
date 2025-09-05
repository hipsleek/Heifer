open Typedhip

(** Functions for rendering formulas, terms, etc. with spacing and indentation.

  {b Note:} The underlying library used to implement these pretty-printers is incompatible with [Format]
    (see {{:github.com/fpottier/pprint/issues/9}this issue} for details). Using their output within
    [Format]'s printing functions may lead to unintuitive line break placements.
*)

(** { 1 Pretty-printer configuration } *)

type config

(** A reasonable starting configuration, with formatting enabled, a column width of 80
    and type annotations disabled. *)
val default_config : config

(** The current global configuration. This is initialized to [default_config], and
    can be changed using [set_current_config]. *)
val current_config : unit -> config

(** Mutate the current configuration. *)
val set_current_config : (config -> config) -> unit

(** Disable line breaks and indentation, leaving all output on a single line.
    This overrides [set_column_width]. *)
val set_single_line : ?enabled:bool -> config -> config

(** Enable type annotations (of terms, binders, etc.) in the output. *)
val set_types_display : ?enabled:bool -> config -> config

(** Set the maximum length of one line of the printer's output. *)
val set_column_width : int -> config -> config

(** { 1 String converters } *)

(** All converters accept an optional [?config] argument, which defaults to [current_config]. *)

(** Note that this is intended to display human-readable output. If 
    you need to obtain the underlying identifier, use [Typedhip.ident_of_binder] instead. *)
val string_of_binder : ?config:config -> binder -> string

val string_of_type : ?config:config -> typ -> string
val string_of_term : ?config:config -> term -> string
val string_of_pi : ?config:config -> pi -> string
val string_of_kappa : ?config:config -> kappa -> string
val string_of_state : ?config:config -> state -> string
val string_of_pattern : ?config:config -> pattern -> string
val string_of_core_lang : ?config:config -> core_lang -> string
val string_of_staged_spec : ?config:config -> staged_spec -> string


(* some other combinators *)
val string_of_option : ?none:string -> ('a -> string) -> 'a option -> string
val string_of_list : ?sep:string -> ('a -> string) -> 'a list -> string

(* these don't really belong here... in common maybe? *)
val string_of_pred : ?config:config -> pred_def -> string
val string_of_abs_env : ?config:config -> Hipcore_common.Types.abs_typ_env -> string
val string_of_type_declaration : ?config:config -> Hipcore_common.Types.type_declaration -> string
