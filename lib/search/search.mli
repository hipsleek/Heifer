(** A small library for proof search and building proof trees.

    {1 Continuations}

    Continuations are used to implement backtracking.

    For example:

    {[
      let f : int -> (int -> unit) -> unit =
        fun x k ->
          k (x + 1);
          k (x + 2)
    ]}

    [f] is in continuation-passing style.
    It can be thought of as a function which "returns" zero or more times by calling [k].
*)

(** [let@] is a useful combinator for working with functions in CPS.
    It allows us to call [f] as if it nondeterministically returns many times:

    {[
      let g () =
        let@ x = g 3 in
        print_int x
    ]}

    This will print [4] and [5]. It desugars as follows:

    {[
      let g () =
        g 3 (fun x -> print_int x)
    ]}

    [g] can be itself transformed to CPS if we need to "return" the results we get from [f].
*)
val ( let@ ) : ('a -> 'b) -> 'a -> 'b

(** {1 Partial computations} *)

(** The other ingredient needed in proof search is failure, i.e. partial computations.
    For that we use an option monad (currently not abstract, but it may be changed to something else in future, e.g. a writer of proof trees). *)
type 'a t = 'a option

(** Bind and map *)

val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

(** Success and failure *)

val ok : 'a -> 'a t
val succeed : unit t
val fail : 'a t

(** Other operations *)

(** Whether a computation succeeded or not *)
val succeeded : 'a t -> bool

(** Succeeds or fails depending on the boolean argument given. *)
val ensure : bool -> unit t

(** Runs [b] if [a] fails.
  {[
    let@ _ = a |> or_else in
    b
  ]}
*)
val or_else : 'a t -> (unit -> 'a t) -> 'a t

(** {1 Searching and proof trees} *)

(** [all ~name ~to_s items f] is a partial computation which succeeds if for {e all} items [i] in [items], [f i] succeeds.
    [name] and [to_s] are used for printing. *)
val all :
  name:string -> to_s:('a -> string) -> 'a list -> ('a -> 'b t) -> unit t

(** Like [all], but threads a state parameter of type ['b] through computations.
    [pivot] and [on_end] allow the state to be transformed in between switching branches and at the end respectively. *)
val all_state :
  name:string ->
  to_s:('a -> string) ->
  init:'b ->
  ?pivot:('b -> 'b) ->
  ?on_end:('b -> 'b) ->
  'a list ->
  ('a * 'b -> 'b t) ->
  'b t

(** [any ~name ~to_s items f] is a partial computation which succeeds if for {e any} item [i] in [items], [f i] succeeds.
    [name] and [to_s] are used for printing. *)
val any : name:string -> to_s:('a -> string) -> 'a list -> ('a -> 'b t) -> 'b t

(** [any] and [all] (statefully record and) log the state of the proof search.
    Call this to clear all state between searches. *)
val reset : unit -> unit
