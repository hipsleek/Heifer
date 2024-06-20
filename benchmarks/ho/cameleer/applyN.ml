
let rec applyN
  ((inv : int -> 'a -> bool)[@ghost]) ((i : int)[@ghost]) ((n0:int)[@ghost])
  (f:'a -> 'a) (x:'a) (n:int) : 'a
=
  if n = 0 then x
  else
    let r = f x in
    applyN inv (i+1) n0 f r (n-1)
(*@ r = applyN inv i n0 f x n
      variant n
      requires 0 <= n
      requires n0 = n + i
      requires inv i x
      requires forall j:int, x:'a. inv j x -> inv (j+1) (f x)
      ensures inv n0 r *)

(*

  ghost variables:

  - n0 is the initial value of n
  - i is the number of applications of f that has occurred so far
  - inv is a property that is true of every x (the input and output of f) given that some number of applications of f has occurred
    
  n decreases, so has to be bounded

  Example

    applyN (inv 0 0) 2 incr 0 2
  = applyN (inv 1 (incr 0)) 2 incr (incr 0) 1
  = applyN (inv 2 (incr (incr 0))) 2 incr (incr (incr 0)) 0
  = (incr (incr 0))
  = 2

  n0 = n + i is invariant

*)

let summary n =
  applyN (fun a x -> x = a) 0 n (fun x -> x + 1) 0 n
(*@ r = summary n
      requires 0 <= n
      ensures r = n *)

let summary1 n =
  applyN (fun a x -> x = 2 * a) 0 n (fun x -> x + 2) 0 n
(*@ r = summary1 n
      requires 0 <= n
      ensures r = 2 * n *)
