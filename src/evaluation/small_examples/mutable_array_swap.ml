effect Swap : int array * int * int -> unit

let swap (arr, i, j)
= perform (Swap (arr, i, j))

let swap_handler (arr, i, j)
= 
  let temp = arr.(i) in
  arr.(i) <- arr(j);
  arr.(j) <- temp

let main ()
= 
  let arr = [|1; 2; 3; 4; 5|] in
  match swap (arr, 0, 1) with
  | v -> v
  | effect (Swap (arr, i, j)) k -> swap_handler(arr, i, j); (continue k ());
  arr;