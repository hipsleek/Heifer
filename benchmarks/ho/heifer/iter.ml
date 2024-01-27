let rec integers x n =
  if n = 0 then []
  else x :: integers (x + 1) (n - 1)

let rec fill_list f n =
  if n = 0 then []
  else f () :: fill_list f (n - 1)

let build_fill x n
(*@ ex i; req x->i; ex r; integers(i, n, r) @*)
= let counter =
    fun () ->
      let r = !x in
      x := !x + 1;
      r
  in
  fill_list counter n
