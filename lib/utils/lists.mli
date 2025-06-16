val unsnoc : 'a list -> 'a list * 'a
val foldr1 : ?default:'a -> ('a -> 'a -> 'a) -> 'a list -> 'a
val foldl1 : ('a -> 'a -> 'a) -> 'a list -> 'a
val replace_nth : int -> 'a -> 'a list -> 'a list
val init : 'a list -> 'a list
val find_delete_opt : ('a -> bool) -> 'a list -> ('a * 'a list) option
val find_delete_map : ('a -> 'b option) -> 'a list -> ('b * 'a list) option
val map_state : ('s -> 'a -> 'b * 's) -> 's -> 'a list -> 'b list * 's
