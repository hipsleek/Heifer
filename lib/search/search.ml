open Debug

let ( let@ ) f x = f x

type 'a t = 'a option

let ( let* ) = Option.bind
let ( let+ ) a f = Option.map f a
let succeeded = Option.is_some
let ok a = Some a
let succeed = Some ()
let fail = None
let check b = if b then succeed else fail
let or_else o k = match o with None -> k () | Some _ -> o
let of_bool default b = if b then Some default else None
let ensure cond = if cond then succeed else fail

type mut_tree =
  | Node of {
      name : string;
      kind : string option;
      mutable state : [ `Done | `NotStarted | `Here | `Failed | `Started ];
      mutable children : mut_tree ref list;
    }

let rule ?(children = []) ?(success = true) ~name ~kind fmt =
  Format.kasprintf
    (fun s ->
      Node
        {
          kind;
          name =
            Format.asprintf "[%s]%s %s" name (if success then "" else " FAIL") s;
          state = `NotStarted;
          children;
        })
    fmt

let empty_tree () =
  Node { name = "root"; children = []; state = `NotStarted; kind = None }

let tree_root = empty_tree ()

(* this is a pointer to the node we are at (`Here) *)
let current = ref tree_root

let reset () =
  let (Node n) = tree_root in
  n.children <- [];
  n.state <- `NotStarted;
  current := tree_root

let string_of_search_state s =
  match s with
  | `Done -> "✔"
  (* ✓o$ *)
  | `NotStarted -> "?"
  | `Here -> "←" (* <- *)
  | `Started -> "…" (* "..." *)
  | `Failed -> "✘" (* x✗ *)

let rec tree_of_mut_tree ?(compact = false) t =
  match t with
  | Node { name; children; state; kind } ->
    Tree.Node
      ( kind,
        Format.asprintf "%s %s" (string_of_search_state state) name,
        match (compact, state) with
        | true, `Done -> []
        | _ -> List.map (fun t -> tree_of_mut_tree ~compact !t) children )

let show_search_tree compact =
  Tree.string_of_proof (tree_of_mut_tree ~compact tree_root)

(** creates subproblems, mutates them into current root, returns them via k, and after completion, restores root before returning.

  this is in cps form because it has some finalization, not because it backtracks; any and all are responsible for that *)
let init_undone kind name vs to_s k =
  let undone =
    List.mapi
      (fun i v ->
        let kind =
          match (i, kind) with
          | 0, `All -> Some "∀"
          | 0, `Any -> Some "∃"
          | _ -> None
        in
        ref (rule ~name ~kind "%s" (to_s v)))
      vs
  in
  let old_current = current in
  let (Node n) = !current in
  n.state <- `Started;
  n.children <- undone;
  let r = k undone in
  (* exceptions are not handled *)
  (match r with None -> n.state <- `Failed | Some _ -> n.state <- `Done);
  (* restore current, though sometimes not needed *)
  current := !old_current;
  r

(** makes a given node the current node *)
let update_current u =
  current := !u;
  let (Node n) = !current in
  n.state <- `Here

(** finalize current node as done *)
let current_done () =
  let (Node n) = !current in
  n.state <- `Done

(** finalize current node as failed *)
let current_failed () =
  let (Node n) = !current in
  n.state <- `Failed

(* allows state to be threaded through branches on success.
   pivot allows the user to change the state between the end of one branch and the start of the next.
   the initial state is init, and on_end allows the state to be changed when all branches complete. *)
let all_state :
    name:string ->
    to_s:('a -> string) ->
    init:'b ->
    ?pivot:('b -> 'b) ->
    ?on_end:('b -> 'b) ->
    'a list ->
    ('a * 'b -> 'b t) ->
    'b t =
 fun ~name ~to_s ~init ?(pivot = Fun.id) ?(on_end = Fun.id) items f ->
  (* items is not labelled to avoid partial application warnings *)
  let rec loop z s undone =
    match (s, undone) with
    | [], _ -> Some (on_end z)
    | x :: xs, u :: us ->
      update_current u;
      debug ~at:1 ~title:"proof search" "%s" (show_search_tree true);
      let r = f (x, pivot z) in
      (match r with
      | None ->
        current_failed ();
        None
      | Some r1 ->
        current_done ();
        loop r1 xs us)
    | _ :: _, [] -> failwith "won't happen because same length"
  in
  let@ undone = init_undone `All (Format.asprintf "%s" name) items to_s in
  loop init items undone

(* simpler version that collects all outputs *)
let all_ :
    name:string -> to_s:('a -> string) -> 'a list -> ('a -> 'b t) -> 'b list t =
 fun ~name ~to_s items f ->
  all_state ~name ~to_s ~init:[] ~on_end:List.rev items (fun (v, st) ->
      let* s = f v in
      ok (s :: st))

(* even simpler version that ignores all outputs *)
let all :
    name:string -> to_s:('a -> string) -> 'a list -> ('a -> 'b t) -> unit t =
 fun ~name ~to_s items f -> all_ ~name ~to_s items f |> Option.map (fun _ -> ())

let any : name:string -> to_s:('a -> string) -> 'a list -> ('a -> 'b t) -> 'b t
    =
 fun ~name ~to_s vs f ->
  match vs with
  | [] ->
    (* Error (rule ~name "choice empty") *)
    (* failwith (Format.asprintf "choice empty: %s" name) *)
    fail
  | _ :: _ ->
    let rec loop vs undone =
      match (vs, undone) with
      | [], _ -> fail
      | v :: vs1, u :: us ->
        update_current u;
        debug ~at:1 ~title:"proof search" "%s" (show_search_tree true);
        let res = f v in
        begin
          match res with
          | None ->
            current_failed ();
            loop vs1 us
          | Some r ->
            current_done ();
            Some r
        end
      | _ :: _, [] -> failwith "won't happen because same length"
    in
    let@ undone = init_undone `Any name vs to_s in
    loop vs undone

let either :
    name:string ->
    (* to_s:(bool -> string) -> *)
    (bool -> 'b option) ->
    'b option =
 fun ~name f -> any ~name ~to_s:string_of_bool [true; false] f
