
include Untyped_core_ast

include Hipcore_common.Data.Make(Untyped_core_ast)

include Common

type 'a quantified = string list * 'a

type instantiations = (string * string) list

let primitive_functions = ["+"; "-"; "*"; "="; "not"; "::"; "&&"; "||"; ">"; "<"; ">="; "<="; "^"; "string_of_int"]
