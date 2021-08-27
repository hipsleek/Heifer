effect Foo : (int -> int -> int)

let f ()
= let a = perform Foo in
  let b = a 1 in
  Format.printf "a 1@.";
  let c = b 2 in
  Format.printf "a 1 2%d@." c;
  c

let res_f
  =
  match (f ()) with
  | x -> x
  | effect Foo k ->
     (* continue k (fun a b -> print_endline "abc"; a + b) *)
     print_endline "got Foo";
     continue k (fun a ->
      print_endline "got a";
      perform Foo |> ignore;
      print_endline "after performing";
      fun b -> print_endline "got b"; a + b)
