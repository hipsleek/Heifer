open Core
open Util.Strings

type 'a t = Pstate.t -> ('a * Pstate.t, string) Result.t

let run m s = m s
let run_pstate m s = Result.map snd (m s)

let printf fmt =
  Format.kasprintf
    (fun s ->
      fun st ->
       print_endline s;
       Ok ((), st))
    fmt

let fail s = fun _ -> Error s
let failf fmt = Format.kasprintf fail fmt
let pure x = fun s -> Ok (x, s)
let map f m = fun s -> Result.map (fun (x, s) -> (f x, s)) (m s)
let mapl x m = fun s -> Result.map (fun (_, s) -> (x, s)) (m s)
let bind m f = fun s -> Result.bind (m s) (fun (x, s) -> f x s)
let ( <$> ) = map
let ( <$ ) = mapl
let ( <&> ) m f = map f m
let ( >>= ) = bind
let ( let+ ) m f = map f m
let ( let* ) = bind

let choice m1 m2 =
 fun s ->
  let r = m1 s in
  match r with
  | Ok _ -> r
  | Error _ -> m2 s

let rec choices ?(err = "empty choice") ms =
 fun s ->
  match ms with
  | [] -> Error err
  | m :: ms ->
      let r = m s in
      (match r with
      | Ok _ -> r
      (* TODO possibly use a list or tree of errors *)
      | Error e -> Result.map_error (Format.asprintf "%s / %s" e) (choices ~err ms s))

let rec map_m f = function
  | [] -> pure []
  | x :: xs ->
      let* y = f x in
      let* ys = map_m f xs in
      pure (y :: ys)

let rec iter_m f = function
  | [] -> pure ()
  | x :: xs ->
      let* _ = f x in
      iter_m f xs

let iter_array_m f xs =
  let l = Array.length xs in
  let rec loop i =
    if i < l then
      let* _ = f (Array.unsafe_get xs i) in
      loop (i + 1)
    else pure ()
  in
  loop 0

let catch m h =
 fun s ->
  let r = m s in
  match r with
  | Ok _ -> r
  | Error e -> h e s

let try_ m =
 fun s ->
  match m s with
  | Ok (x, s) -> Ok (Ok x, s)
  | Error e -> Ok (Error e, s)

let get = fun s -> Ok (s, s)
let put s = fun _ -> Ok ((), s)
let gets f = fun s -> Ok (f s, s)
let modify f = fun s -> Ok ((), f s)
let map_error f m = fun s -> Result.map_error f (m s)

let pop_pctxt =
  let* ps = get in
  match ps with
  | [] -> fail "no more goal"
  | p :: ps -> p <$ put ps

let push_pctxt p = modify (fun ps -> p :: ps)

let dup_pctxt =
  let* ps = get in
  match ps with
  | [] -> fail "no more goal"
  | p :: _ -> put (p :: ps)

let get_pctxt =
  let* ps = get in
  match ps with
  | [] -> fail "no more goal"
  | p :: _ -> pure p

let put_pctxt p =
  let* ps = get in
  match ps with
  | [] -> fail "no more goal"
  | _ :: ps -> put (p :: ps)

let gets_pctxt f =
  let* ps = get in
  match ps with
  | [] -> fail "no more goal"
  | p :: _ -> pure (f p)

let modify_pctxt f =
  let* ps = get in
  match ps with
  | [] -> fail "no more goal"
  | p :: ps -> put (f p :: ps)

let get_rename_ctxt = gets_pctxt (fun p -> p.Pctx.rename_ctxt)
let get_constants = gets_pctxt (fun p -> p.Pctx.constants)
let get_assumptions = gets_pctxt (fun p -> p.Pctx.assumptions)
let get_heap_assumptions = gets_pctxt (fun p -> p.Pctx.heap_assumptions)
let get_goal = gets_pctxt (fun p -> p.Pctx.goal)

module Message = struct
  let does_not_exist = Format.sprintf "%s does not exist"
  let is_already_used = Format.sprintf "%s is already used"
end

let get_constant name =
  let* constants = get_constants in
  match SMap.find_opt name constants with
  | None -> fail ("get_constant: " ^ Message.does_not_exist name)
  | Some v -> pure v

let get_assumption name =
  let* assumptions = get_assumptions in
  match SMap.find_opt name assumptions with
  | None -> fail ("get_assumption: " ^ Message.does_not_exist name)
  | Some t -> pure t

(* let get_heap_assumption name =
    let* heap_assumptions = get_heap_assumptions in
    match SMap.find_opt name heap_assumptions with
    | None -> fail ("no heap assumption named: " ^ name)
    | Some t -> return t *)

let put_rename_ctxt rename_ctxt = modify_pctxt (fun p -> { p with Pctx.rename_ctxt })
let put_constants constants = modify_pctxt (fun p -> { p with Pctx.constants })
let put_assumptions assumptions = modify_pctxt (fun p -> { p with Pctx.assumptions })

let put_assumption name p =
  let* _ = get_assumption name in
  let* assumptions = get_assumptions in
  put_assumptions (SMap.add name p assumptions)

let put_heap_assumptions heap_assumptions = modify_pctxt (fun p -> { p with Pctx.heap_assumptions })
let put_goal goal = modify_pctxt (fun p -> { p with Pctx.goal })

let add_constant name v =
  let* constants = get_constants in
  if SMap.mem name constants then fail ("add_constant: " ^ Message.is_already_used name)
  else put_constants (SMap.add name v constants)

let add_assumption name t =
  if Names.is_underscore name then pure ()
  else
    let* assumptions = get_assumptions in
    if SMap.mem name assumptions then fail ("add_assumption: " ^ Message.is_already_used name)
    else put_assumptions (SMap.add name t assumptions)

(* let add_heap_assumption name t =
    let* heap_assumptions = get_heap_assumptions in
    if SMap.mem name heap_assumptions
    then fail ("add_heap_assumption: " ^ name ^ " is already used")
    else put_heap_assumptions (SMap.add name t heap_assumptions) *)

let pop_assumption name =
  let* assumptions = get_assumptions in
  match SMap.find_opt name assumptions with
  | None -> fail ("pop_assumption: " ^ Message.does_not_exist name)
  | Some t -> t <$ put_assumptions (SMap.remove name assumptions)

(* let pop_heap_assumption name =
    let* heap_assumptions = get_heap_assumptions in
    match SMap.find_opt name heap_assumptions with
    | None -> fail ("no heap assumption named: " ^ name)
    | Some t ->
        let+ _ = put_heap_assumptions (SMap.remove name heap_assumptions) in
        t *)

let modify_goal f = modify_pctxt (fun p -> { p with Pctx.goal = f p.Pctx.goal })

let modify_heap_assumptions f =
  modify_pctxt (fun p -> { p with Pctx.heap_assumptions = f p.Pctx.heap_assumptions })
