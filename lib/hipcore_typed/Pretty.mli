open Typedhip

(** { 1 Pretty-printer configuration } *)

type config

val default_config : unit -> config

val set_single_line : ?enabled:bool -> config -> config

val set_types_display : ?enabled:bool -> config -> config

val set_column_width : int -> config -> config

(** { 1 String converters } *)

(** Note that this is intended to display human-readable output. If 
    you need to obtain the underlying identifier, use [ident_of_binder] instead. *)
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
