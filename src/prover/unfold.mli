open Core.Syntax
open Bindlib

(** [unfold sym def t] unfolds all applications of the symbol [sym] inside the
    term [t], using the definition [def]. *)
val unfold : symbol -> (term, term) mbinder -> term -> term
