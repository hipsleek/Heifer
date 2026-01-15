let rec integers x n =
  if n = 0 then []
  else x :: integers (x + 1) (n - 1)

let rec fill_list f n =
  if n = 0 then []
  else f () :: fill_list f (n - 1)

(* this cannot be proved because fill_list depends on i through counter,
   so the rewrite fails *)

let build_fill_false i n
(*@ ex r; integers(i, n, r) @*)
= let counter =
    let x = ref i in
    fun () ->
      let r = !x in
      x := !x + 1;
      r
  in
  fill_list counter n

(* what would work is to parameterize by the location *)

let build_fill x n
(*@ ex i; req x->i; ex r; integers(i, n, r) @*)
= let counter =
    fun () ->
      let r = !x in
      x := !x + 1;
      r
  in
  fill_list counter n
