(* 0: no output except results
   1: high-level output to explain to a user what is going on
   2 and above: for developers, higher levels give more detail *)
let debug_level = ref 0
let debug_event_n = ref 0
let stack = ref []
let advanced = ref true
let pp_event ppf r = Format.fprintf ppf "_%d" r
let is_closing = ref false

let summarize_stack () =
  (* String.concat "@"
     (!stack |> List.rev |> List.map (fun i -> Format.asprintf "%a" pp_event i)) *)
  match !stack with [] -> "" | e :: _ -> Format.asprintf "%a" pp_event e

let debug_print title s =
  let title =
    let stack =
      if not !is_closing then ""
      else Format.asprintf " <-%s" (summarize_stack ())
    in
    Format.asprintf "%s | %a%s" title pp_event !debug_event_n stack
  in
  if String.length title < 6 then print_string (Pretty.yellow title ^ " ")
  else print_endline (Pretty.yellow title);
  print_endline s;
  if not (String.equal "" s) then print_endline ""

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
  show None;
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
