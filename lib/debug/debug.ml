let ( let@ ) f x = f x

(* 0: no output except results
   1: high-level output to explain to a user what is going on
   2 and above: for developers, higher levels give more detail *)
(* let debug_level = ref 0 *)
let debug_event_n = ref 0
let stack : (string * int) list ref = ref []
let pp_event ppf r = Format.fprintf ppf "_%d" r
let is_closing = ref false
let is_opening = ref false
let last_title = ref ""
let ctf_output = ref false
let file_mode = ref false

let yellow text =
  match !file_mode with
  | false -> "\u{001b}[33m" ^ text ^ "\u{001b}[0m"
  | true -> text

module Buffered = struct
  let buffered_event : (string * string * int) option ref = ref None

  let write_line title s =
    print_endline (yellow title);
    print_endline s;
    if not (String.equal "" s) then print_endline ""

  let buffer_event title s n = buffered_event := Some (title, s, n)
  let clear_buffer () = buffered_event := None

  let flush_buffer () =
    match !buffered_event with
    | None -> ()
    | Some (title, s, _) ->
      clear_buffer ();
      write_line title s

  let collapse_empty_spans title s =
    match !buffered_event with
    | Some (_, _, _) when !is_closing ->
      (* we assume events are well-bracketed.
         on closing a span, if there's something in the buffer, we must have left it there. *)
      clear_buffer ();
      write_line title s
    | None when !is_closing ->
      (* something must have occurred which cleared the buffer before us, so output normally *)
      write_line title s
    | _ when !is_opening ->
      flush_buffer ();
      buffer_event title s !debug_event_n
    | _ ->
      flush_buffer ();
      write_line title s
end

let may_fail f = try Some (f ()) with _ -> None
let parses f = Option.is_some (may_fail f)

module Query = struct
  type query_on =
    | Time of int
    | Range of int * int
    | Regex of string * Str.regexp
    | LogLevel of int
    | All (* to avoid a catch-all regex *)

  type query_action =
    | Hide
    | Show

  type query = (query_action * query_on * bool) list

  (** terrible parser for a ;-separated string *)
  let parse_query s =
    let parts = Str.split (Str.regexp {|[ ]*;[ ]*|}) s in
    let regex =
      Str.regexp
        {|\(h\|s\|hr\|sr\) \(\([0-9]+\)-\([0-9]+\)\|\([0-9]+\)\|\(.*\)\)\|\([0-9]+\)|}
    in
    (* let parts =
         (* extract debug level *)
         match parts with
         | s :: rest ->
           (try
              debug_level := int_of_string s;
              rest
            with _ -> parts)
         | [] -> parts
       in *)
    let parts =
      List.concat_map
        (fun p ->
          if Str.string_match regex p 0 then
            match () with
            | _ when parses (fun () -> Str.matched_group 7 p) ->
              let l = Str.matched_group 7 p |> int_of_string in
              [(Show, LogLevel l, false)]
            | _ ->
              let action, recursive =
                match Str.matched_group 1 p with
                | "s" -> (Show, false)
                | "h" -> (Hide, false)
                | "sr" -> (Show, true)
                | "hr" -> (Hide, true)
                | (exception _) | _ -> failwith "invalid action"
              in
              let on =
                match () with
                | _ when parses (fun () -> Str.matched_group 3 p) ->
                  Range
                    ( Str.matched_group 3 p |> int_of_string,
                      Str.matched_group 4 p |> int_of_string )
                | _ when parses (fun () -> Str.matched_group 5 p) ->
                  Time (Str.matched_group 5 p |> int_of_string)
                | _ when parses (fun () -> Str.matched_group 6 p) ->
                  let s = Str.matched_group 6 p in
                  Regex (s, Str.regexp_case_fold s)
                | (exception _) | _ -> failwith "invalid on"
              in
              [(action, on, recursive)]
          else failwith "unable to parse query")
        parts
    in
    (* let exceptions escape *)
    Some parts

  let string_of_query_action a = match a with Hide -> "Hide" | Show -> "Show"

  let string_of_query_on o =
    match o with
    | Time i -> Format.asprintf "Time(%d)" i
    | Range (a, b) -> Format.asprintf "Range(%d, %d)" a b
    | Regex (s, _) -> Format.asprintf "Regex(%s)" s
    | LogLevel l -> Format.asprintf "LogLevel(%d)" l
    | All -> "All"

  let string_of_list p xs =
    match xs with
    | [] -> "[]"
    | _ ->
      let a = List.map p xs |> String.concat "; " in
      Format.asprintf "[%s]" a

  let string_of_query qs =
    string_of_list
      (fun (action, on, recursive) ->
        Format.asprintf "(%s, %s, %b)"
          (string_of_query_action action)
          (string_of_query_on on) recursive)
      qs

  let user_query : query ref = ref []
  let collapse i = (Hide, Time i, true)
  let expand i = (Show, Time i, true)
  let whitelist r = (Show, Regex (r, Str.regexp_case_fold r), false)
  let blacklist r = (Hide, Regex (r, Str.regexp_case_fold r), false)

  let affects at title time (_, on, recursive) =
    match (on, recursive) with
    | LogLevel i, _ -> at <= i
    | Regex (_, r), false -> Str.string_match r title 0
    | Regex (_, r), true ->
      List.exists (fun (t, _e) -> Str.string_match r t 0) !stack
      || Str.string_match r title 0
    | Time t, true -> List.exists (fun (_, t1) -> t1 = t) !stack || t = time
    | Time t, false -> t = time
    | Range (s, e), true ->
      List.exists (fun (_, t) -> s <= t && t <= e) !stack
      || s = time || e = time
    | Range (s, e), false -> s <= time && time <= e
    | All, _ -> true

  let interpret at title time qs =
    List.rev qs
    |> List.find_map (fun ((action, _, _) as q) ->
           let af = affects at title time q in
           match (af, action) with
           | true, Show -> Some true
           | true, Hide -> Some false
           | false, _ -> None)
    |> Option.value ~default:false
end

open Query

let in_debug_mode () = match !user_query with [] -> false | _ :: _ -> true
let trace_out = ref None

let summarize_stack () =
  (* String.concat "@"
     (!stack |> List.rev |> List.map (fun i -> Format.asprintf "%a" pp_event i)) *)
  match !stack with [] -> "" | (_t, e) :: _ -> Format.asprintf "%a" pp_event e

let debug_print at title s =
  last_title := title;
  (* the query can filter ctf output, but only one of ctf or trace output is shown *)
  let show = interpret at title !debug_event_n !user_query in
  match show with
  | false -> ()
  | true ->
    (match !ctf_output with
    | false ->
      let title =
        let stack =
          if not !is_closing then ""
          else Format.asprintf " <-%s" (summarize_stack ())
        in
        Format.asprintf "%s | %a%s" title pp_event !debug_event_n stack
      in
      let title =
        match !file_mode with
        | false -> Format.asprintf "==== %s ====" title
        | true ->
          Format.asprintf "%s %s"
            (String.init (List.length !stack + 1) (fun _ -> '*'))
            title
      in
      begin
        let should_buffer = true in
        match should_buffer with
        | true -> Buffered.collapse_empty_spans title s
        | false -> Buffered.write_line title s
      end
    | true ->
      let typ = if !is_closing then "E" else if !is_opening then "B" else "i" in
      let scope = if !is_closing || !is_opening then "" else {|,"s":"t"|} in
      let json_scrub s =
        s
        |> Str.global_replace (Str.regexp "\n") " "
        |> Str.global_replace (Str.regexp {|\\|}) {|\\\\|}
      in
      let s = json_scrub s in
      let title = json_scrub title in
      Format.fprintf (!trace_out |> Option.get)
        {|{"name": "%s", "tid": 1, "ts": %f, "ph": "%s", "args": {"txt": "%s"}%s},@.|}
        title
        (Sys.time () *. 1000. *. 1000.)
        typ s scope)

(* someday https://github.com/ocaml/ocaml/pull/126 *)
let debug ~at ~title fmt =
  Format.kasprintf
    (fun s ->
      (* if !debug_level >= at then *)
      debug_print at title s;
      incr debug_event_n)
    fmt

module Res = struct
  type 'a t =
    | NoValueYet
    | Value of 'a
    | Exn of exn

  let map f a =
    match a with
    | NoValueYet -> NoValueYet
    | Exn e -> Exn e
    | Value a -> Value (f a)
end

open Res

let span show k =
  let start = !debug_event_n in

  (* let sum1 = summarize_stack () in *)
  (* let args = *)
  (* { stack = sum1; event = start } *)
  is_opening := true;
  show NoValueYet;
  is_opening := false;
  (* in *)
  stack := (!last_title, start) :: !stack;
  (* Format.printf "%s@." args; *)
  match k () with
  | r ->
    (* let stop = !debug_event_n in *)
    (* let sum2 = summarize_stack () in *)
    (* { stack = sum2; event = stop } *)

    (* this is safe because the user is only supposed to call debug inside here, not do further recursion, so this is just a way of communicating non-locally across functions in this module *)
    is_closing := true;
    show (Value r);
    is_closing := false;

    stack := List.tl !stack;
    (* Format.printf "%s@." ; *)
    r
  | exception e ->
    (* https://ocamlpro.com/blog/2024_04_25_ocaml_backtraces_on_uncaught_exceptions/#reraising *)
    let bt = Printexc.get_raw_backtrace () in
    is_closing := true;
    show (Exn e);
    is_closing := false;

    stack := List.tl !stack;
    (* Format.printf "%s@." ; *)
    Printexc.raise_with_backtrace e bt

let pp_result f ppf r =
  match r with
  | NoValueYet -> Format.fprintf ppf "..."
  | Value r -> Format.fprintf ppf "%a" f r
  | Exn e -> Format.fprintf ppf "%s" (Printexc.to_string e)

let string_of_result f r =
  match r with
  | NoValueYet -> "..."
  | Exn e -> Printexc.to_string e
  | Value r -> Format.asprintf "%s" (f r)

let init ~ctf ~org query =
  at_exit (fun () -> Buffered.flush_buffer ());
  file_mode := org;
  if ctf then (
    ctf_output := true;
    let name = "trace.json" in
    Format.printf "%s@." name;
    let oc = open_out name in
    trace_out := Some (Format.formatter_of_out_channel oc);
    Format.fprintf (!trace_out |> Option.get) "[@.");
  user_query :=
    query |> (fun o -> Option.bind o parse_query) |> Option.value ~default:[]

let%expect_test _ =
  let test_program () =
    let f x =
      let@ _ =
        span (fun r ->
            debug ~at:2
              ~title:(Format.asprintf "%s" "hi")
              "%s ==> %s" (string_of_int x)
              (string_of_result string_of_int r))
      in
      debug ~at:1 ~title:"aaa" "%s" "b";
      x + 1
    in
    debug ~at:1 ~title:"before" "%s" "b";
    ignore @@ f 2;
    debug ~at:1 ~title:"after" "%s" "b"
  in

  let test q =
    (* debug_level := 3; *)
    debug_event_n := 0;
    user_query := q;
    Format.printf "-----@.";
    Format.printf "%s@." (string_of_query q);
    Format.printf "-----@.";
    test_program ()
  in

  test [];
  test [whitelist "aa"];
  test [blacklist "aa"];
  test [(Show, All, false); collapse 1; whitelist "aaa"];
  test (parse_query "h .*; s aa" |> Option.get);
  test [expand 1];
  test [whitelist "aa"; blacklist ".*"; whitelist ".*efo"];
  test [whitelist "aa"; blacklist "aa"];
  test [whitelist "aa"; blacklist "aa"; whitelist "aa"];
  test [(Show, Range (1, 2), true)];

  [%expect
    {|
    -----
    []
    -----
    -----
    [(Show, Regex(aa), false)]
    -----
    ==== aaa | _2 ====
    b

    -----
    [(Hide, Regex(aa), false)]
    -----
    -----
    [(Show, All, false); (Hide, Time(1), true); (Show, Regex(aaa), false)]
    -----
    ==== before | _0 ====
    b

    ==== aaa | _2 ====
    b

    ==== after | _4 ====
    b

    -----
    [(Hide, Regex(.*), false); (Show, Regex(aa), false)]
    -----
    ==== aaa | _2 ====
    b

    -----
    [(Show, Time(1), true)]
    -----
    ==== hi | _1 ====
    2 ==> ...

    ==== aaa | _2 ====
    b

    ==== hi | _3 <-_1 ====
    2 ==> 3

    -----
    [(Show, Regex(aa), false); (Hide, Regex(.*), false); (Show, Regex(.*efo), false)]
    -----
    ==== before | _0 ====
    b

    -----
    [(Show, Regex(aa), false); (Hide, Regex(aa), false)]
    -----
    -----
    [(Show, Regex(aa), false); (Hide, Regex(aa), false); (Show, Regex(aa), false)]
    -----
    ==== aaa | _2 ====
    b

    -----
    [(Show, Range(1, 2), true)]
    -----
    ==== hi | _1 ====
    2 ==> ...

    ==== aaa | _2 ====
    b

    ==== hi | _3 <-_1 ====
    2 ==> 3
    |}]
