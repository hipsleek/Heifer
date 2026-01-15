module Monad : sig
  val pure : 'a -> 'a option
  val ( let+ ) : 'a option -> ('a -> 'b) -> 'b option
  val ( let* ) : 'a option -> ('a -> 'b option) -> 'b option
end

val filter : ('a -> bool) -> 'a option -> 'a option
