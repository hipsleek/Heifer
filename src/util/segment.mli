module Seg : sig
  type t
  val length : int * int -> int
  val mem : 'a -> 'a * 'a -> bool
  val compare : int * 'a -> int * 'b -> int
end

module SegSet : Set.S with type elt = Seg.t

module SegTree : sig
  type t
  val empty : SegSet.t
  val add : int -> SegSet.t -> SegSet.t
  val mem : int -> SegSet.t -> bool
  val remove : int -> SegSet.t -> SegSet.t
  val length : SegSet.t -> int
  val union : SegSet.t -> SegSet.t -> SegSet.t
  val next : int -> SegSet.t -> int
  val max_elt_opt : SegSet.t -> int option
end
