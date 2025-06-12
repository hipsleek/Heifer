val unsnoc : 'a list -> 'a list * 'a
val foldr1 : ?default:'a -> ('a -> 'a -> 'a) -> 'a list -> 'a
val foldl1 : ('a -> 'a -> 'a) -> 'a list -> 'a
val replace_nth : int -> 'a -> 'a list -> 'a list
val init : 'a list -> 'a list
val find_delete_opt : ('a -> bool) -> 'a list -> ('a * 'a list) option
