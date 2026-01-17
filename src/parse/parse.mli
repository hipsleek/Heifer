open Core.Syntax
open Util.Strings
open Bindlib

val parse_term : ?ctx:term var SMap.t -> string -> term
val parse_prop : ?ctx:term var SMap.t -> string -> prop
val parse_hprop : ?ctx:term var SMap.t -> string -> hprop
val parse_staged_spec : ?ctx:term var SMap.t -> string -> staged_spec
val parse_decl : string -> decl
