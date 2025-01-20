(**

A small library for structured logging and tracing.

To use this, a user manually instruments their code with [debug] and [span], to indicate when events occur,
and provides a query at runtime to say which events to emit.
The emitted events are written to a file in plain text, org, or {{: https://docs.google.com/document/d/1CvAClvFfyA5R-PhYUmn5OOQtYMH4h6I0nSsKchNAySU/preview#heading=h.yr4qxyxotyw }Chrome Trace Format} (CTF) for viewing with {{: https://ui.perfetto.dev/ }Perfetto}.

{1 Queries}

A query has the following syntax:

{v
  Q ::= <int> | cmd <regex> | Q ; Q
  cmd ::= s | h | sr | hr
v}

{ul {- [<int>]: show events with <= debug level }
    {- s: show events whose titles match the given {{: https://ocaml.org/manual/5.2/api/Str.html }regex}}
    {- h: hide events with matching titles; as everything is hidden by default, this only has an effect after showing something }
    {- sr: show recursively }
    {- hr: hide recursively }
    {- [;]: sequential composition, i.e. later commands have precedence }}

{1 API}

*)

(** [init ~ctf ~org query] initializes the library,
    where [ctf] enables production of trace data in CTF,
    [query] is a query string for controlling what is logged, setting debug levels, etc., and
    [org] is true for org-mode output and false for more human-readable output. *)
val init : ctf:bool -> org:bool -> string option -> unit

(** [debug ~at:log_level ~title fmt] outputs an instantaneous event. *)
val debug :
  at:int -> title:string -> ('a, Format.formatter, unit, unit) format4 -> 'a

val ( let@ ) : ('a -> 'b) -> 'a -> 'b

(** Partial/pending results: the result of a function call at a point in time.
    Either it has not materialized yet, or has and is a value or exception. *)
type 'a presult =
  | NoValueYet
  | Value of 'a
  | Exn of exn

val map_presult : ('a -> 'b) -> 'a presult -> 'b presult

(** Output a span. Example usage:

    {[
      let f param : v =
        let@ _ = Debug.span (fun r ->
          debug ~at:3 ~title:"f" "f %s => %s"
            (string_of_param param) (string_of_result string_of_v r))
        in
        <body>
    ]}

    Given a call [f 1], this will produce [f 1 => ?] before [body] executes and [f 1 => res] after.
    Intervening events will be nested inside the span.
*)
val span : ('a presult -> unit) -> (unit -> 'a) -> 'a

(** Returns true iff debug logging is enabled, which requires a query to be provided. *)
val in_debug_mode : unit -> bool

val string_of_result : ('a -> string) -> 'a presult -> string

val pp_result :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a presult -> unit

module Query : sig
  type query_on =
    | Time of int
    | Range of int * int
    | Regex of string * Str.regexp
    | LogLevel of int
    | All (* to avoid a catch-all regex *)

  type query_action =
    | Hide
    | Show

  type query = (query_action * query_on * bool) list
  
  val user_query : query ref
end
