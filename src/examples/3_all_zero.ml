
let main ()
(*@ Norm(emp, 0) @*)
=
(* let (mutlist:(((int ref) list) ref)) = ref [ref 2] *)
  let mutlist = ref [ref 2] in

  (* let set_all_zero li = List.map (fun a -> a := 0) (!li)  ;; *)
  let rec set_all_zero li =
    match !li with
    | [] -> ()
    | x :: xs -> x := 0; set_all_zero (ref xs)
    (* List.map (fun a -> a := 0) (!li)  ;; *)
  in
  set_all_zero mutlist;
  assert (!mutlist = [ref 0]);
  0