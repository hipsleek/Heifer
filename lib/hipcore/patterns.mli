open Typedhip

type guarded_pattern = pattern * term

(** Given a pattern [P], and a list of other patterns [L], return a list of patterns
   that cover all terms that match P, but not any pattern in [L]. *)
val exclude : guarded_pattern -> guarded_pattern list -> guarded_pattern list

(** Generates a pure formula corresponding to [pat_term]
matching under the pattern. The corresponding list is
the free variables in the formula. *)
val pi_of_pattern : term -> guarded_pattern -> binder list * pi
