let succ x = x + 1

let iter_map_succ x i
(*@ integers(i, n, r) @*)
=
  let counter =
    fun () ->
      let r = !x in
      x := !x + 1;
      r
  in
  (* this definition is coinductive? *)
  let iter_map f it =
    fun () -> f (it ())
  in
  iter_map succ counter

let itzz n =
  fill_list counter n



(*@ ex i; req x->i; ex r; integers(i, n, r) @*)
= let counter =
    fun () ->
      let r = !x in
      x := !x + 1;
      r
  in
  fill_list counter n
