
(* https://patrick.sirref.org/posts/escaping-effects 


# try
    try raise Not_found with (Invalid_argument _) -> print_endline "invalid_arg"
  with
    Not_found -> print_endline "not_found"; invalid_arg "Woops";;
not_found
Exception: Invalid_argument "Woops".

*)



effect GetName : string
effect Env : unit -> unit

let test () = 
  perform GetName

let rec handler1 () = 
  match test () with
  | v -> ()
  | effect (Env _) k -> print_endline "" 

let handler = 
  match handler1 () with 
  | v -> ()
  | effect GetName k -> perform (Env (continue k "Alice")) 

