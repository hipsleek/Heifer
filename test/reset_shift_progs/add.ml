let rec add a b
= if a == 0 then b else add (a - 1) (b + 1)

(*@
  lemma add_lemma a b res =
    add(a, b, res) ==> ens res=a + b
 @*)

let main ()
(*@ ens res = 20 @*)
= add 10 10

let rec add_shift a b
= if a == 0 then shift k (k b) else add_shift (a - 1) (b + 1)

(*@
  lemma add_shift_lemma res =
    reset(ex v104; ex v102; ens emp; add_shift(10, 10, v102); ens v104=v102; ens res=v104, res) ==> ens res=20
 @*)

let main_shift ()
(*@ ens res = 20 @*)
= reset (let x = add_shift 10 10 in x)
