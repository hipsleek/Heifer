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

(** A rewriter is means of transforming a "large" type ['l] by rewriting a
    subterm of "small" type ['s] within it. *)
type ('l, 's) rewriter

val rewrite_all : ('a, 'b) rewriter -> ('b, 'c, 'b) pattern -> 'c -> 'a -> 'a
val pi_in_staged : (staged_spec, pi) rewriter
val pi_in_pi : (pi, pi) rewriter
val staged : (staged_spec, staged_spec) rewriter

(** {1 Rules and databases} *)

(** A rule is a means of rewriting a subterm of type ['a] to another of the same
    type within some larger data structure. It is a LHS pattern for matching and
    a continuation which allows creating a RHS. *)
type ('a, 'k) rule = ('a, 'k, 'a) pattern * 'k

(** A database of rewrite rules. The first parameter is the type of data that
    rules in this database act on, e.g. [pi]. The second is a sequence of
    continuation types encoded as a function (as in typical heterogeneous
    lists). *)
type (_, _) database =
  | [] : ('a, unit) database
  | ( :: ) : ('a, 'k) rule * ('a, 'elts) database -> ('a, 'k -> 'elts) database

val autorewrite : ('l, 's) rewriter -> ('s, 'k) database -> 'l -> 'l

(** {1 Heifer's AST} *)

val true_ : (pi, 'a, 'a) pattern
val false_ : (pi, 'a, 'a) pattern
val and_ : (pi, 'a, 'b) pattern -> (pi, 'b, 'c) pattern -> (pi, 'a, 'c) pattern
val string : string -> (string, 'b, 'b) pattern
val binder : string -> (string, 'b, 'b) pattern
val var : string -> (term, 'b, 'b) pattern

val req :
  (pi, 'a, 'b) pattern ->
  (kappa, 'b, 'c) pattern ->
  (staged_spec, 'a, 'c) pattern

val ens :
  (pi, 'a, 'b) pattern ->
  (kappa, 'b, 'c) pattern ->
  (staged_spec, 'a, 'c) pattern

val disj :
  (staged_spec, 'a, 'b) pattern ->
  (staged_spec, 'b, 'c) pattern ->
  (staged_spec, 'a, 'c) pattern

val seq :
  (staged_spec, 'a, 'b) pattern ->
  (staged_spec, 'b, 'c) pattern ->
  (staged_spec, 'a, 'c) pattern

val bind :
  (string, 'a, 'b) pattern ->
  (staged_spec, 'b, 'c) pattern ->
  (staged_spec, 'c, 'd) pattern ->
  (staged_spec, 'a, 'd) pattern

val reset :
  (staged_spec, 'a, 'b) pattern ->
  (staged_spec, 'a, 'b) pattern

val eq :
  (term, 'a, 'b) pattern -> (term, 'b, 'c) pattern -> (pi, 'a, 'c) pattern

val emp : (kappa, 'a, 'a) pattern
