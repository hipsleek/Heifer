
let awkward =
  let r = ref 0 in
  fun f -> assert (!r mod 2 = 0); incr r; f(); incr r

let () =
  ignore (awkward (fun () -> ignore (awkward (fun () -> ()))))
