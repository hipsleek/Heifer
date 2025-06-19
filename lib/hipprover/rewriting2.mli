open Hipcore
open Hiptypes

(** Inspired by ppxlib's Ast_pattern.
    https://ocaml-ppx.github.io/ppxlib/ppxlib/matching-code.html
    https://github.com/ocaml-ppx/ppxlib/blob/main/src/ast_pattern0.ml
    https://github.com/ocaml-ppx/ppxlib/blob/main/src/ast_pattern.ml *)

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

val rewrite_all_staged :
  (staged_spec, 'a, staged_spec) pattern -> 'a -> staged_spec -> staged_spec

val rewrite_all_pi_in_pi : (pi, 'a, pi) pattern -> 'a -> pi -> pi

(** {1 Rules and databases} *)

(** A rule is a means of rewriting a subterm of type ['a] to another of the same
    type within some larger data structure. It is a pair of a LHS pattern for
    matching, and a continuation which allows generating a RHS. *)
type ('a, 'k) rule = ('a, 'k, 'a) pattern * 'k

(** A database of rewrite rules. The first parameter is the type of data rules
    in this db act on, e.g. [pi]. The second is a sequence of continuation types
    encoded as a function (as in typical heterogeneous lists). *)
type (_, _) db =
  | [] : ('a, unit) db
  | ( :: ) : ('a, 'k) rule * ('a, 'elts) db -> ('a, 'k -> 'elts) db

val autorewrite_pi : (pi, 'k) db -> pi -> pi
val autorewrite : (staged_spec, 'k) db -> staged_spec -> staged_spec

(** {1 Heifer's AST} *)

val true_ : (pi, 'a, 'a) pattern
val false_ : (pi, 'a, 'a) pattern
val and_ : (pi, 'a, 'b) pattern -> (pi, 'b, 'c) pattern -> (pi, 'a, 'c) pattern
val string : string -> (string, 'b, 'b) pattern
val binder : string -> (string, 'b, 'b) pattern
val var : string -> (term, 'b, 'b) pattern

val ens :
  (pi, 'a, 'b) pattern ->
  (kappa, 'b, 'c) pattern ->
  (staged_spec, 'a, 'c) pattern

val bind :
  (string, 'a, 'b) pattern ->
  (staged_spec, 'b, 'c) pattern ->
  (staged_spec, 'c, 'd) pattern ->
  (staged_spec, 'a, 'd) pattern

val eq :
  (term, 'a, 'b) pattern -> (term, 'b, 'c) pattern -> (pi, 'a, 'c) pattern

val emp : (kappa, 'a, 'a) pattern
