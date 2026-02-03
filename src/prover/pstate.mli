type t = Pctx.t list

val destruct : 'a list -> 'a list list
val focus : 'a list -> 'a list * 'a list
val append : 'a list -> 'a list -> 'a list
val pp : Format.formatter -> Pctx.t list -> unit
