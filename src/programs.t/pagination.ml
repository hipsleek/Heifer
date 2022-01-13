
let sublist low high list =
   List.filteri (fun i _ -> i >= low && i < high) list

type 'a res = Res of 'a * (unit -> 'a res)

effect Request : int -> (string list) res
effect ContinueFrom : int * int -> (string list) res

let get n = perform (Request n)
let get_from n = perform (ContinueFrom (n, n))

let database_server client =
  let database = List.init 30 (Format.sprintf "data%d") in
  match client () with
  | () -> ()
  | effect (Request n) k ->
    let results = sublist 0 n database in
    continue k (Res (results, fun () -> get_from n))
  | effect (ContinueFrom (start, size)) k ->
    let results = sublist start (start + size) database in
    continue k (Res (results, fun () -> perform (ContinueFrom (start + size, size))))

let client () =
  print_endline "First page of results:";
  let Res (results, next) = get 10 in
  List.iter print_endline results;
  print_endline "\nGetting next page...";
  let Res (results, next) = next () in
  List.iter print_endline results

let () =
  database_server client