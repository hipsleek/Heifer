module Core : sig
  type t
  val length : t -> int
  val mem : int -> t -> bool
  val compare : t -> t -> int
end

module Set : Set.S with type elt = Core.t

module Tree : sig
  type t
  val empty : t
  val add : int -> t -> t
  val mem : int -> t -> bool
  val remove : int -> t -> t
  val length : t -> int
  val union : t -> t -> t
  val next : int -> t -> int
  val fresh : int -> t -> int * t
  val max_elt_opt : t -> int option
end
