
(* NUS CS1101S Reading Assessment 1 20/21 S1 *)
let capture_u_and_override_v u v
(*@ ens res=u+12 @*)
= let foo u = let v = 4 in u + v + 3 in
  foo (u + 5)

let call_g_in_f w
(*@ ens res=w*.4+4 @*)
= let g x = w + x in
  let f w = g w + g w in
  f (w + 2)

let define_g_in_f w
(*@ ens res=4*.w+8 @*)
= let f w =
    let x = 3 in
    (* FIXME: Scoping issue here where x=3 *)
    let g x = w + x in
    g w + g w in
  f (w + 2)

let chain_of_functions y z x w
(*@ ens res=y+z+x+w @*)
= let f () = fun y -> fun z -> fun x -> fun w -> y + z + x + w in
  f () y z x w

let call_g_and_h_in_f x y
(*@ ens res=7-y+4+x @*)
= let foo g h x y = g x + h y in
  foo (fun x -> x - y) (fun y -> x + y) 7 4

let call_f_in_g ()
(*@ ens res=5 @*)
= let g f = (fun x -> f x) in
  g (fun x -> x + 1) 4

let nested_lambdas x y (* FIXME: Possible issues with scoping *)
(*@ ens res=3*.x+y+14 @*)
= let f = (fun x y ->
    let outer = (fun y -> y x + 1) in
    let inner = (fun x -> x + x + x + y) in
    outer inner
  ) in
  f (x + 4) (y + 1)
