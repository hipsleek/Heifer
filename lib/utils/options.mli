val concat_option : 'a option list -> 'a list

module Syntax : sig
  val ( let* ) : 'a option -> ('a -> 'b option) -> 'b option
  val ( let+ ) : 'a option -> ('a -> 'b) -> 'b option
end
