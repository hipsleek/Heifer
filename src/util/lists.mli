module Monad : sig
  val pure : 'a -> 'a list
  val ( let+ ) : 'a list -> ('a -> 'b) -> 'b list
  val ( let* ) : 'a list -> ('a -> 'b list) -> 'b list
end

val unsnoc : 'a list -> 'a list * 'a
val fold_left1 : ('a -> 'a -> 'a) -> 'a list -> 'a
val fold_right1 : ('a -> 'a -> 'a) -> 'a list -> 'a
val set_nth : int -> 'a -> 'a list -> 'a list
val init : 'a list -> 'a list
val find_remove_opt : ('a -> bool) -> 'a list -> ('a * 'a list) option
val find_remove_map : ('a -> 'b option) -> 'a list -> ('b * 'a list) option
val product : 'a list -> 'b list -> ('a * 'b) list
