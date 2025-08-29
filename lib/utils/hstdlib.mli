module SSet : sig
  include Set.S with type elt = string

  val concat : t list -> t
  val to_list : t -> string list
end

module SMap : sig
  include Map.S with type key = string

  val keys : 'a t -> string list
  val values : 'a t -> 'a list
  
  val merge_disjoint : 'a t -> 'a t -> 'a t
  val merge_right_priority : 'a t -> 'a t -> 'a t
  val merge_arbitrary : 'a t -> 'a t -> 'a t

  val merge_all_disjoint : 'a t list -> 'a t

  val intersect : 'a t -> 'a t -> 'a t

  val of_list : (string * 'a) list -> 'a t
end
