let toss x
= shift k (x := !x + 1; let r1 = k true in
           x := !x + 1; let r2 = k false in
           r1 + r2)

let foo x
(*@ forall a. req x -> a; ens x -> a + 2; ens res = 1 @*)
= reset (let v = toss x in if v then 1 else 0)
