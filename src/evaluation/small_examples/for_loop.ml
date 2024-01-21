effect Incr : int

let incr ()
(*@
  ex ret;
  Incr(emp, ret);
  Norm(emp, ret)
@*)
= perform Incr

let for_loop () =
  let i = ref 0 in
  for _ = 0 to 10 do
    match incr () with
    | effect Incr k -> i := !i + 1; (continue k ())
  done;