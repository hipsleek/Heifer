effect Read : int 
effect Write : int -> unit 

let read () =
  let n = perform Read in
  perform (Write 2)
  (* perform Read *)

let main ()
= match read () with
  | v ->
    Format.printf "normal %d@." v;
    v
  | effect Read k ->
    Format.printf "read handler@.";
    let v = continue k 1 in
    Format.printf "read %d@." v;
    v + 1
  | effect (Write n) k ->
    Format.printf "write handler %d@." n;
    let v = continue k () in
    Format.printf "write %d@." v;
    v

let () = ignore (main ())
