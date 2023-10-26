open Effect.Deep
open Multicont.Deep

type _ Effect.t += Test : unit  Effect.t

let test () = 
  Effect.perform Test;
  Effect.perform Test

let queue_create () = ref ([], []) 

let queue_push ele queue = 
  let (front, back) = !queue in 
  queue := (front, ele::back)

let queue_is_empty queue = 
  let (front, back) = !queue in 
  List.length front = 0 && List.length back = 0

let rev_list l =
  let rec rev_acc acc = function
    | [] -> acc
    | hd::tl -> rev_acc (hd::acc) tl
  in 
  rev_acc [] l

let queue_pop queue = 
  let (front, back) = !queue in 
  match front with 
  | h::tl -> 
    queue := (tl, back); 
    h 
  | [] -> 
    (match rev_list back with 
    | [] -> raise (Failure "dequeue-ing an empty queue")
    | h::newfront -> 
        queue := (newfront, []); 
        h)

let _ = 
  let run_q = queue_create () in
  let enqueue k = queue_push k run_q in
  let dequeue () =
    if queue_is_empty run_q then 
      (print_endline ("empty equeue");
      () )
    else resume (queue_pop run_q) ()
  in

  match_with test () (* n *)
    { retc = (fun _ -> 
      dequeue ();
      )
    ; exnc = (fun e -> raise e)
    ; effc = (fun (type a) (eff : a Effect.t) ->
      match eff with
      | Test -> 
        print_endline ("handling test");
        Some (fun (k : (a, _) continuation) -> 
          let r = promote k in
          enqueue r; 
          enqueue r; 
          dequeue ()
        )
      | _ -> None) }
