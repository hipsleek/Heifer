val choice : ('a, 'e) result -> ('a, 'e) result -> ('a, 'e) result

module Monad : sig
  val pure : 'a -> ('a, 'e) result
  val ( let+ ) : ('a, 'e) result -> ('a -> 'b) -> ('b, 'e) result
  val ( let* ) : ('a, 'e) result -> ('a -> ('b, 'e) result) -> ('b, 'e) result
end
