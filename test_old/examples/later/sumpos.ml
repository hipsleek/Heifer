let rec nonzero xs =
  match xs with
  | [] -> true
  | x :: xs1 -> if x = 0 then false else nonzero xs1

let rec sumpos xs =
  match xs with
  | [] -> true
  | x :: xs1 -> if x > 0 then x + sumpos xs1 else sumpos xs1

(* foldr_with_f1$(a,l,res) =
         req nozero(l); ens sumpos(l,a,res)
         \/ req ~nozero(l); Exception(_) *)
let foldr_with_f1 init xs
(*@ ex r; nonzero(xs,r); ens r=true; sumpos(xs,res) \/ ex r; nonzero(xs, r); ens r=false; E @*)
= let f1 c t = if c = 0 then perform E else if c > 0 then c + t else t in
  foldr f1 xs init
