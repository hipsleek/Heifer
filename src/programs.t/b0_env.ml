effect Foo : (unit -> unit)

let foo _ () = print_string ("Foo\n") ; perform Foo ()

let f g = let a = g 1 in a ()

let main = 
  match f (foo) with 
  | _ -> ()
  | effect Foo k -> continue k (fun () -> ())

