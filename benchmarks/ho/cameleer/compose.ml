let compose f g x = f (g x)
(*@ y = compose f g x
      ensures y = f (g x)
*)

let compose_pure () = compose (fun x -> x + 1) (fun x -> x * 2) 3
(*@ y = test1 ()
      ensures y = 7
*)
