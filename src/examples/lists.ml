
let rec map f xs =
  match xs with
  | [] -> []
  | x :: xs1 -> f x :: map f xs1

let incr x = x + 1

let id y = y

let map_id ys
(*@ Norm(emp, ys) @*)
= map id ys

let x = ref 0 ;; 

let cl n = x := x + 1 ; n 

(* Norm (x -> a /\ l = length(li) /\ ret=list' /\ list'=li, li)  *)
let map_cl cl_in li = 
  let l = List.length li in 
  let list' = List.map (fun a -> cl_in a) li in 
  assert (!x = l); 
  list'


(* fold_rec (acc, f, li, r) = 
li = nil /\ Norm(ret = acc, ret) 
\/
li = x :: xs /\ f$(acc, x, r_f); fold_rec$(r_f, f, xs, r) 
*)
let rec fold_rec acc f li = 
  match li with 
  | [] -> acc 
  | x ::xs -> 
    let acc' = f acc x in 
    fold_rec acc' f xs 

let rec fold_rec acc f li inv = 
  match li with 
  | [] -> inv li acc; acc 
  | x ::xs -> 
    let acc' = f acc x in 
    fold_rec acc' f xs 
    
(* 
Norm (ret = init+ List.sum(li), ret)
*)
let fold_client init li = fold_rec init (fun acc a -> acc + a) li

(*
base case: li = [] -> Norm(ret = 0, ret) 
inductive case: li = x::xs -> 
  Norm(r_f = acc+x, r_f); Norm (ret = List.sum(xs), r = r_f+ret)

  fold_rec$(r_f, f, xs) 
*)
li = x :: xs =>  x + List.sum(xs) = list.sum(li)