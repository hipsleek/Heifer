let sublist low high list =
   List.filteri (fun i _ -> i >= low && i < high) list

type 'a page = Page of 'a * (unit -> 'a page)

effect Request : int * int -> (string list) page

effect Done : (string list) page

let make_request n = perform (Request (0, n))

let database_server client
  (*@ requires _^* *)
  (*@ ensures Request^*.Done *)
=
  let database = List.init 30 (Format.sprintf "data%d") in
  let db_size = List.length database in
  match client () with
  | () -> ()
  | effect Done k ->
    (* close the connection *)
    continue k (Page ([], fun () -> perform Done))
  | effect (Request (start, size)) k ->
    let results, next =
      if start < db_size then
        sublist start (min (start + size) db_size) database,
        (* remember the page size and dynamically determine the next continuation.
          this splits control over both handler and client. *)
        (fun () -> perform (Request (start + size, size)))
      else
        [],
        (fun () -> perform Done)
    in
    continue k (Page (results, next))

let client () =
  print_endline "First page of results:";
  let Page (results, next) = make_request 10 in
  List.iter print_endline results;
  print_endline "\nGetting next page...";
  let Page (results, next) = next () in
  List.iter print_endline results

let client1 () =
  let rec loop n (Page (results, next)) =
    match results with
    | [] -> print_endline "end"
    | _ ->
      Format.printf "\nPage %d@." n;
      List.iter print_endline results;
      loop (n + 1) (next ())
  in
  loop 1 (make_request 10)

let () =
  database_server client;
  print_endline "---";
  database_server client1;

