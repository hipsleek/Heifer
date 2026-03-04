let either a b =
  shift (fun k -> k a; k b)

let [@spec "ex r. ens r -> 3; ens res = 3"] main () =
  let r = ref 0 in
  (reset (let x = either 1 2 in r := !r + x));
  (* (reset (let x = either 3 4 in r := !r + x)); *)
  (* if we add the line above, heifer will throw an error in verification time *)
  !r
