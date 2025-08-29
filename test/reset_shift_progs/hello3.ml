let [@spec "ens res = 3"] hello3 () =
  let f x = x + x in
  reset (1 + shift (fun k -> (k (f 1))))
