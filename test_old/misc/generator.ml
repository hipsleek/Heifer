
effect Next : int -> unit

let to_gen iter t =
  let rec step = ref (fun () ->
    try
      iter (fun x -> perform (Next x)) t;
      None
    with effect (Next v) k ->
      step := (fun () -> continue k ());
      Some v)
  in
    fun () -> !step ()


let[@warning "-8"] f () =
  let next = to_gen List.iter [1; 2; 3] in
  let Some a = next () in
  let Some b = next () in
  Format.printf "%d %d@." a b;
  let Some c = next () in
  Format.printf "%d@." c;
  let None = next () in
  Format.printf "ok@."

let () = f ()