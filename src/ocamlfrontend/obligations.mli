open Core.Syntax
open Core_lang

type t = (term list * term) list

(** Generates proof obligations in a "triangular" manner, e.g.

    {[
      let fn1 : f1 = e1
      let fn2 : f2 = e2
    ]}

    produces two obligations

    {v
      forward e1 <: f1


      forward e1 <: f1
      --------------------
      forward e2 <: f2
    v} *)
val generate : verification_unit -> t
