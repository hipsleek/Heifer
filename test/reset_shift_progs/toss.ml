let toss x
= shift k (x := !x + 1; let r1 = k true in
           x := !x + 1; let r2 = k false in
           r1 && r2)

let foo x
(*@ forall a. req x -> a; ens x -> a + 2; ens res = false @*)
= reset (let v = toss x in if v then true else false)

(*
let rec toss_n n x
= if n = 1 then
    toss x
  else
    let r1 = toss x in
    let r2 = toss_n (n - 1) x in
    r1 && r2

let foo_n n x
(*@ forall a. req x -> a; req n > 0; ex b. ens x -> b; ens b > a + n; ens res = false @*)
= reset (let v = toss_n n x in if v then true else false)
*)
