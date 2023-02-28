
(* Example taken from https://github.com/ocaml-multicore/effects-examples/blob/master/multishot/clone_is_tricky.ml *)

effect A : unit
effect B : unit

let run () =
  match perform A with
  | effect A k ->
    perform B;
    continue k ()
  | _ -> ()

let () =
  match run () with
  | effect B k ->
    continue (Obj.clone_continuation k) ();
    continue k ()
  | _ -> ()
