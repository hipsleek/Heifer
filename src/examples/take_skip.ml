
(* let (mutlist:(((int ref) list) ref)) = ref [ref 1; ref 2; ref 3; ref 4] *)

(* let rec take n li =
  (* (li:(int ref) list) : (int ref) list  =  *)
  if n = 0 then []
  else 
    (match li with 
    | [] -> []
    | x :: xs -> 
      x :: take (n-1) xs)

let rec skip n li =
  (* (li:(int ref) list) : (int ref) list  =  *)
  if n = 0 then li 
  else 
    (match li with 
    | [] -> []
    | _ :: xs -> 
      skip (n-1) xs) *)

      (* ;; *)

(* mutlist := take_n  3 (!mutlist);;
mutlist := skip_n  2 (!mutlist);;

assert (!mutlist = [ref 3]);; *)
  (* (n:nat) (xs:list nat) := *)
  (* (n:nat) (xs:list nat) := *)

let rec take n xs =
  if n = 0 then []
  else
    (match xs with
    | [] -> []
    | x :: xs1 -> x :: take (n-1) xs1)

let rec skip n xs =
  if n = 0 then xs
  else
    (match xs with
    | [] -> []
    | x :: xs1 -> skip (n-1) xs1)

(* the induction hypothesis should be: forall xs. skip n (take n xs) = [] *)

let take_skip n xs
(*@ Norm(emp, []) @*)
= skip n (take n xs)
