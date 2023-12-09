(* 0: no output except results
   1: high-level output to explain to a user what is going on
   2 and above: for developers, higher levels give more detail *)
let debug_level = ref 0
let debug_event_n = ref 0
let stack = ref []
let advanced = ref true
let pp_event ppf r = Format.fprintf ppf "_%d" r
let is_closing = ref false
let is_opening = ref false
let blacklist = Sys.getenv_opt "BLACKLIST" |> Option.map Str.regexp_case_fold
let whitelist = Sys.getenv_opt "WHITELIST" |> Option.map Str.regexp_case_fold
let collapse = Sys.getenv_opt "COLLAPSE" |> Option.map Str.regexp_case_fold

type query_on =
  | Time of int
  | Range of int * int
  | Regex of string * Str.regexp

type query_action =
  | Hide
  | Show

type query = (query_action * query_on) list

(** terrible parser for a ;-separated string *)
let parse_query s =
  let parts = Str.split (Str.regexp {| *; *|}) s in
  let regex =
    Str.regexp {|\(h\|s\) \(\([0-9]+\)-\([0-9]+\)\|\([0-9]+\)\|\(.*\)\)|}
  in
  try
    let parts =
      List.map
        (fun p ->
          if Str.string_match regex p 0 then
            let hs =
              match Str.matched_group 1 p with
              | "s" -> Show
              | "h" -> Hide
              | (exception _) | _ -> failwith "invalid"
            in
            let other =
              match () with
              | _
                when try
                       ignore (Str.matched_group 3 p);
                       true
                     with Not_found -> false ->
                Range
                  ( Str.matched_group 3 p |> int_of_string,
                    Str.matched_group 4 p |> int_of_string )
              | _
                when try
                       ignore (Str.matched_group 5 p);
                       true
                     with Not_found -> false ->
                Time (Str.matched_group 5 p |> int_of_string)
              | _
                when try
                       ignore (Str.matched_group 6 p);
                       true
                     with Not_found -> false ->
                let s = Str.matched_group 6 p in
                Regex (s, Str.regexp_case_fold s)
              | (exception _) | _ -> failwith "invalid"
            in
            (hs, other)
          else failwith "unable to parse")
        parts
    in
    Some parts
  with Failure _ -> None

let string_of_query_action a = match a with Hide -> "Hide" | Show -> "Show"

let string_of_query_on o =
  match o with
  | Time i -> Format.asprintf "Time(%d)" i
  | Range (a, b) -> Format.asprintf "Range(%d, %d)" a b
  | Regex (s, _) -> Format.asprintf "Regex(%s)" s

let string_of_query qs =
  Common.string_of_list
    (fun (action, on) ->
      Format.asprintf "(%s, %s)"
        (string_of_query_action action)
        (string_of_query_on on))
    qs

let user_query : query ref =
  ref
    (Sys.getenv_opt "QUERY"
    |> (fun o -> Option.bind o parse_query)
    |> Option.value ~default:[])

let collapse i = (Hide, Time i)
let expand i = (Show, Time i)
let whitelist r = (Show, Regex (r, Str.regexp_case_fold r))
let blacklist r = (Hide, Regex (r, Str.regexp_case_fold r))
let trace_out = ref None

let summarize_stack () =
  (* String.concat "@"
     (!stack |> List.rev |> List.map (fun i -> Format.asprintf "%a" pp_event i)) *)
  match !stack with [] -> "" | e :: _ -> Format.asprintf "%a" pp_event e

(* affects can return if it's directly or indirectly (as a child) affected, for more granular control *)
let affects title time (_, o) =
  match o with
  | Regex (_, r) -> Str.string_match r title 0
  | Time t -> List.mem t !stack || t = time
  | Range (s, e) ->
    List.exists (fun t -> s <= t && t <= e) !stack || s = time || e = time

let rec interpret title time qs =
  List.rev qs
  |> List.find_map (fun q ->
         let af = affects title time q in
         match (af, fst q) with
         | true, Show -> Some true
         | true, Hide -> Some false
         | false, _ -> None)
  |> Option.value ~default:true

let ctf = false
(* let ctf = true *)

let debug_print title s =
  let title =
    match ctf with
    | false ->
      let stack =
        if not !is_closing then ""
        else Format.asprintf " <-%s" (summarize_stack ())
      in
      Format.asprintf "%s | %a%s" title pp_event !debug_event_n stack
    | true -> title
  in
  let show = interpret title !debug_event_n !user_query in
  match show with
  | false -> ()
  | true ->
    (match ctf with
    | false ->
      if String.length title < 6 then print_string (Pretty.yellow title ^ " ")
      else print_endline (Pretty.yellow title);
      print_endline s;
      if not (String.equal "" s) then print_endline ""
    | true ->
      let typ = if !is_closing then "E" else if !is_opening then "B" else "i" in
      let scope = if !is_closing || !is_opening then "" else {|,"s":"t"|} in
      let scrub s =
        s
        |> Str.global_replace (Str.regexp "\n") ""
        |> Str.global_replace (Str.regexp {|\\|}) {|\\\\|}
      in
      let s = scrub s in
      let title = scrub title in
      Format.fprintf (!trace_out |> Option.get)
        {|{"name": "%s", "tid": 1, "ts": %f, "ph": "%s", "args": {"txt": "%s"}%s},@.|}
        title
        (Sys.time () *. 1000. *. 1000.)
        typ s scope)

(* someday https://github.com/ocaml/ocaml/pull/126 *)
let debug ~at ~title fmt =
  Format.kasprintf
    (fun s ->
      if !debug_level >= at then debug_print title s;
      incr debug_event_n)
    fmt

(** info output is shown to the user *)
let info ~title fmt = debug ~at:1 ~title fmt

type ctx = {
  event : int;
  stack : string;
}

(* let get_event () =
   let r = !debug_event_n in
   incr debug_event_n;
   r *)

let pp_opening ppf r =
  match r with None -> () | Some r -> Format.fprintf ppf "%a" pp_event r

let span show k =
  let start = !debug_event_n in

  (* let sum1 = summarize_stack () in *)
  (* let args = *)
  (* { stack = sum1; event = start } *)
  is_opening := true;
  show None;
  is_opening := false;
  (* in *)
  stack := start :: !stack;
  (* Format.printf "%s@." args; *)
  let r = k () in

  (* let stop = !debug_event_n in *)
  (* let sum2 = summarize_stack () in *)
  (* { stack = sum2; event = stop } *)

  (* this is safe because the user is only supposed to call debug inside here, not do further recursion, so this is just a way of communicating non-locally across functions in this module *)
  is_closing := true;
  show (Some r);
  is_closing := false;

  stack := List.tl !stack;
  (* Format.printf "%s@." ; *)
  r

let pp_result f ppf r =
  match r with
  | None -> Format.fprintf ppf "..."
  | Some r -> Format.fprintf ppf "%a" f r

let string_of_result f r =
  match r with None -> "..." | Some r -> Format.asprintf "%s" (f r)

let init () =
  if ctf then (
    let oc = open_out "trace.json" in
    trace_out := Some (Format.formatter_of_out_channel oc);
    Format.fprintf (!trace_out |> Option.get) "[@.")

let%expect_test _ =
  let open Common in
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
    debug_level := 3;
    debug_event_n := 0;
    user_query := q;
    Format.printf "-----@.";
    Format.printf "%s@." (string_of_query q);
    test_program ()
  in

  test [];
  test [collapse 1; whitelist "aaa"];
  test [whitelist "aa"];
  (* test [blacklist ".*"; whitelist "aa"]; *)
  test (parse_query "h .*; s aa" |> Option.get);
  test [blacklist ".*"; expand 1];
  test [blacklist ".*"; whitelist "aa"; blacklist ".*"; whitelist ".*efo"];
  test [whitelist "aa"; blacklist "aa"];
  test [whitelist "aa"; blacklist "aa"; whitelist "aa"];
  test [blacklist "aa"];
  test [blacklist ".*"; (Show, Range (1, 2))];

  [%expect
    {|
    -----
    []
    ==== before | _0 ====
    b

    ==== hi | _1 ====
    2 ==> ...

    ==== aaa | _2 ====
    b

    ==== hi | _3 <-_1 ====
    2 ==> 3

    ==== after | _4 ====
    b

    -----
    [(Hide, Time(1)); (Show, Regex(aaa))]
    ==== before | _0 ====
    b

    ==== aaa | _2 ====
    b

    ==== after | _4 ====
    b

    -----
    [(Show, Regex(aa))]
    ==== before | _0 ====
    b

    ==== hi | _1 ====
    2 ==> ...

    ==== aaa | _2 ====
    b

    ==== hi | _3 <-_1 ====
    2 ==> 3

    ==== after | _4 ====
    b

    -----
    [(Hide, Regex(.*)); (Show, Regex(aa))]
    ==== aaa | _2 ====
    b

    -----
    [(Hide, Regex(.*)); (Show, Time(1))]
    ==== hi | _1 ====
    2 ==> ...

    ==== aaa | _2 ====
    b

    ==== hi | _3 <-_1 ====
    2 ==> 3

    -----
    [(Hide, Regex(.*)); (Show, Regex(aa)); (Hide, Regex(.*)); (Show, Regex(.*efo))]
    ==== before | _0 ====
    b

    -----
    [(Show, Regex(aa)); (Hide, Regex(aa))]
    ==== before | _0 ====
    b

    ==== hi | _1 ====
    2 ==> ...

    ==== hi | _3 <-_1 ====
    2 ==> 3

    ==== after | _4 ====
    b

    -----
    [(Show, Regex(aa)); (Hide, Regex(aa)); (Show, Regex(aa))]
    ==== before | _0 ====
    b

    ==== hi | _1 ====
    2 ==> ...

    ==== aaa | _2 ====
    b

    ==== hi | _3 <-_1 ====
    2 ==> 3

    ==== after | _4 ====
    b

    -----
    [(Hide, Regex(aa))]
    ==== before | _0 ====
    b

    ==== hi | _1 ====
    2 ==> ...

    ==== hi | _3 <-_1 ====
    2 ==> 3

    ==== after | _4 ====
    b

    -----
    [(Hide, Regex(.*)); (Show, Range(1, 2))]
    ==== hi | _1 ====
    2 ==> ...

    ==== aaa | _2 ====
    b

    ==== hi | _3 <-_1 ====
    2 ==> 3
    |}]
