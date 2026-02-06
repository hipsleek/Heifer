type t = Pctx.t list

val destruct : t -> t list
val focus : t -> t * t
val append : t -> t -> t
val is_empty : t -> bool
val pp : Format.formatter -> t -> unit
