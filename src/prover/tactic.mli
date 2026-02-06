open Core
open Core.Syntax
open Bindlib
open Util.Strings

(* TODO make abstract *)
type 'a t = Pstate.t -> ('a * Pstate.t, string) Result.t

val run : 'a t -> Pstate.t -> ('a * Pstate.t, string) result
val run_pstate : 'a t -> Pstate.t -> (Pstate.t, string) result

(* basic combinators *)
val pure : 'a -> 'a t
val map : ('a -> 'b) -> 'a t -> 'b t
val mapl : 'b -> 'a t -> 'b t
val lift2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val seql : 'a t -> 'b t -> 'a t
val seqr : 'a t -> 'b t -> 'b t
val bind : 'a t -> ('a -> 'b t) -> 'b t
val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t
val ( <&> ) : 'a t -> ('a -> 'b) -> 'b t
val ( <$ ) : 'b -> 'a t -> 'b t
val ( $> ) : 'a t -> 'b -> 'b t
val ( <* ) : 'a t -> 'b t -> 'a t
val ( *> ) : 'a t -> 'b t -> 'b t
val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
val dbg : string -> unit t
val fail : string -> 'a t
val printf : ('a, Format.formatter, unit, unit t) format4 -> 'a
val failf : ('a, Format.formatter, unit, 'b t) format4 -> 'a
val try_ : 'a t -> ('a, string) result t
val catch : 'a t -> (string -> 'a t) -> 'a t
val choice : 'a t -> 'a t -> 'a t
val choices : ?err:string -> 'a t list -> 'a t
val get : Pstate.t t
val put : Pstate.t -> unit t
val gets : (Pstate.t -> 'a) -> 'a t
val modify : (Pstate.t -> Pstate.t) -> unit t
val map_error : (string -> string) -> 'a t -> 'a t

(* higher-order combinators, with other datatypes *)
val map_m : ('a -> 'b t) -> 'a list -> 'b list t
val map_array_m : ('a -> 'b t) -> 'a array -> 'b list t
val iter_m : ('a -> unit t) -> 'a list -> unit t
val iter_array_m : ('a -> unit t) -> 'a array -> unit t

(* derived combinators: managing pctxts *)
val pop_pctxt : Pctx.t t
val push_pctxt : Pctx.t -> unit t
val dup_pctxt : unit t
val get_pctxt : Pctx.t t
val put_pctxt : Pctx.t -> unit t
val gets_pctxt : (Pctx.t -> 'a) -> 'a t
val modify_pctxt : (Pctx.t -> Pctx.t) -> unit t

(* derived combinators: get *)
val get_rename_ctxt : Rename.ctxt t
val get_constants : term var SMap.t t
val get_assumptions : term SMap.t t
val get_heap_assumptions : term list t
val get_goal : term t
val get_constant : string -> term var t
val get_assumption : string -> term t

(* val get_heap_assumption : string -> term t *)
(* derived combinators: put *)
val put_rename_ctxt : Rename.ctxt -> unit t
val put_constants : term var SMap.t -> unit t
val put_assumptions : term SMap.t -> unit t
val put_assumption : string -> term -> unit t
val put_heap_assumptions : term list -> unit t
val put_goal : term -> unit t
val add_constant : string -> term var -> unit t
val add_assumption : string -> term -> unit t

(* val add_heap_assumption : string -> term -> unit t *)
(* derived combinators: modify *)
val pop_assumption : string -> term t (* remove + return *)

(* val pop_heap_assumption : string -> term t *)
val modify_goal : (term -> term) -> unit t
val modify_heap_assumptions : (term list -> term list) -> unit t
