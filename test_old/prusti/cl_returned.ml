
(* https://github.com/FabianWolff/closure-examples/blob/master/cl_returned.rs *)
let cl_returned ()
(*@ ens res>=0 @*)
= let foo () = let f () = 42 in f in
  let cl = foo () in
  cl ()
