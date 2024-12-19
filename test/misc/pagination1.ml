
let sublist low high list =
   List.filteri (fun i _ -> i >= low && i < high) list

type 'a page = Page of 'a * (unit -> 'a page)

effect Request : int -> (string list) page
effect ContinueFrom : int * int -> (string list) page

let get n = perform (Request n)

let database_server client
  (*@ ensures Request.ContinueFrom^*.(Stop \/ Abort) *)
=
  let database = List.init 30 (Format.sprintf "data%d") in
  match client () with
  | () -> ()
  | effect Abort k ->
    (* closes the connection *)
  | effect Stop k ->
    (* closes the connection *)
  | effect (Request n) k ->
    let results = sublist 0 n database in
    continue k (Page (results, fun () ->
      perform (ContinueFrom (n, n))))
  | effect (ContinueFrom (start, size)) k ->
    let results = sublist start (start + size) database in
    continue k (Page (results, fun () ->
      perform (ContinueFrom (start + size, size))))

    next =
      if n < length database then
        fun () -> perform (ContinueFrom (start + size, size))
      else
        fun () -> perform Abort

    continue k (Page (results, next))

let client () =
  print_endline "First page of results:";
  let Page (results, next) = get 10 in
  List.iter print_endline results;
  print_endline "\nGetting next page...";
  let Page (results, next) = next () in
  List.iter print_endline results

let () =
  database_server client
