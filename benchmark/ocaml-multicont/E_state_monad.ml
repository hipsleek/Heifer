open Printf
open Effect.Deep

type _ Effect.t += Put : int -> unit Effect.t
type _ Effect.t += Get : int Effect.t

let put v = Effect.perform (Put v)
let get () = Effect.perform Get

let rec counter (c : int) =
  let i = get ()
  in if (i==0) 
      then c 
      else (put (i - 1); counter (c + 1))

let _test () = let i = counter 0 in printf "%d\n" i 

let read_n_write ()
= let x = get() in 
  put(x+1);
  let i = get() in 
  printf "%d\n" i 

let _ = 
  let s = ref 1 in
  match_with read_n_write () (* n *)
    { retc = (fun x -> x)
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (eff : a Effect.t) ->
      match eff with
      | Get -> Some (fun (k : (a, _) continuation) -> let i : int = !s in continue k i )
      | Put x -> Some (fun (k : (a, _) continuation) -> s := x; continue k ())
      | _ -> None) }
