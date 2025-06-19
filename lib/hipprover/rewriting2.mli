open Hipcore
open Hiptypes

(** {1 Patterns} *)
type ('matched_value, 'k, 'k_result) pattern

val __ : ('a, 'a -> 'b, 'b) pattern
val drop : ('a, 'b, 'b) pattern
val as__ : ('a, 'b, 'c) pattern -> ('a, 'a -> 'b, 'c) pattern

(** {1 Matching} *)
val match_ : pat:('a, 'b, 'c) pattern -> scr:'a -> rhs:'b -> 'c
val match1 : ('a, 'b -> 'b, 'c) pattern -> 'a -> 'c
val match2 : ('a, 'b -> 'c -> 'b * 'c, 'd) pattern -> 'a -> 'd
val match3 : ('a, 'b -> 'c -> 'd -> 'b * 'c * 'd, 'e) pattern -> 'a -> 'e

(** {1 Rewriting} *)
val rewrite_rooted : lhs:('a, 'b, 'c) pattern -> target:'a -> rhs:'b -> 'c
val rewrite_all_pi : (pi, 'a, pi) pattern -> 'a -> staged_spec -> staged_spec
val rewrite_all_staged : (staged_spec, 'a, staged_spec) pattern -> 'a -> staged_spec -> staged_spec
val rewrite_all_pi_in_pi : (pi, 'a, pi) pattern -> 'a -> pi -> pi

(** {1 Rules and databases} *)
type ('a, 'k) rule = ('a, 'k, 'a) pattern * 'k

type (_, _) db =
  | [] : ('a, unit) db
  | (::) : ('a, 'k) rule * ('a, 'elts) db -> ('a, 'k -> 'elts) db

val autorewrite : (pi, 'k) db -> pi -> pi

(** {1 Heifer's AST} *)
val true_ : (pi, 'a, 'a) pattern
val false_ : (pi, 'a, 'a) pattern
val and_ : (pi, 'a, 'b) pattern -> (pi, 'b, 'c) pattern -> (pi, 'a, 'c) pattern
