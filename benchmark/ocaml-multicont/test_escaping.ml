open Effect.Deep

type _ Effect.t += E1 : unit  Effect.t
type _ Effect.t += E2 : unit  Effect.t

let test () 
(*@ E2; E1@*)
= 
  Effect.perform E2;
  Effect.perform E1

let inner () = 
  (*@ E2@*)
  match_with test () (* n *)
  { retc = (fun _ ->print_endline ("E1 return") ; () )
  ; exnc = (fun e -> raise e)
  ; effc = (fun (type a) (eff : a Effect.t) ->
    match eff with
    | E1 -> 
      Some (fun (k : (a, _) continuation) -> 
        print_endline ("E1 eff") ;
        perform E1;
        continue k ()
      )
    | _ -> None) }

let _ = inner () 

let _test = 
    (*@ @*)
  match_with inner () (* n *)
    { retc = (fun _ -> print_endline ("E2 return") ; () )
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (eff : a Effect.t) ->
      match eff with
      | E2 -> 
        Some (fun (k : (a, _) continuation) -> 
          print_endline ("E2 eff") ;
          continue k ()
        )
      | _ -> None) }
