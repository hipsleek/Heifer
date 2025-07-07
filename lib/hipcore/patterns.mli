open Hiptypes

(** Given a pattern [P], and a list of other patterns [L], return a list of patterns
   that cover all terms that match P, but not any pattern in [L]. *)
val exclude : pattern -> pattern list -> pattern list

(** Generates a pure formula corresponding to [pat_term]
matching under the pattern. The corresponding list is
the free variables in the formula. *)
val pi_of_pattern : term -> pattern -> string list * pi

(** Versions of the functions in this module that support
    _pattern guards_, an additional boolean term that further filters
    the possible values of bound variables. *)
module Guarded : sig
  type t = pattern * term

  val exclude : t -> t list -> t list

  val pi_of_pattern : term -> t -> string list * pi
end
