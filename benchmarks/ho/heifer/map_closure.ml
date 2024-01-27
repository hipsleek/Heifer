
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let rec length xs =
  match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let cl_map xs x
(*@ ex i; req x->i; ex r; length(xs, r); ex r1; ens x->i+r/\r1=xs/\res=r1 @*)
= let f a = x := !x + 1; a in
  map f xs

let rec incr_list init li =
  match li with 
  | [] -> []
  | x :: xs -> 
    init :: incr_list (init + 1) xs

let cl_map_incr_l xs x
(*@ ex i; req x->i; ex r; length(xs, r); ex r1; ens x->i+r/\res=r1 @*)
= let f a = x := !x + 1; !x in
  map f xs

let cl_map_incr_c xs x
(*@ ex i; req x->i; ex ys; ex j; ens j=i+1; incr_list(j, xs, ys); ens res=ys @*)
= let f a = x := !x + 1; !x in
  map f xs
