module Monad : sig
  val pure : 'a -> 'a option
  val ( let+ ) : 'a option -> ('a -> 'b) -> 'b option
  val ( let* ) : 'a option -> ('a -> 'b option) -> 'b option
end

val guard : bool -> unit option
val filter : ('a -> bool) -> 'a option -> 'a option
