
let test1 a
(*@ ens res=3 @*)
= let acc1 y = y + 1 in
  let g1 x = acc1 x in
  g1 2

let f2 z =
  let _ = 1 in
  fun y -> y + 1

let test2 a
(*@ ens res=3 @*)
= let acc2 = f2 1 in
  let g2 x = acc2 x in
  g2 2

(* local unfolding should work as well *)
let test3 a
(*@ ens res>2 @*)
= let acc3 y = y + 1 in
  let g3 x (*@ ens res>x @*) = acc3 x in
  g3 2
