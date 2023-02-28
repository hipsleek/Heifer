
(* Example taken from https://github.com/ocaml-multicore/effects-examples/blob/master/multishot/clone_is_tricky.ml *)

effect One : unit
effect Multi : unit

let run () =
  match perform One with
  | effect One k ->
    perform Multi;
    continue k ()
    (* we get a crash here because One's continuation is resumed
       more than once. When captured by continuations, linear
       resumptions should be treated like resources + assertions. *)
  | _ -> ()

let () =
  match run () with
  | effect Multi k ->
    continue (Obj.clone_continuation k) ();
    continue k ()
  | _ -> ()
