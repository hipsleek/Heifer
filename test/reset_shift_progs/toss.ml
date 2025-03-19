let do_toss x
= shift k (
    x := !x + 1; let r1 = k true in
    x := !x + 1; let r2 = k false in r1 && r2)

let rec do_toss_n x n
= if n = 1 then
    do_toss x
  else
    let r1 = do_toss x in
    let r2 = do_toss_n x (n - 1) in
    r1 && r2

let toss_n x n
= reset (do_toss_n x n)
