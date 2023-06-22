
let rec build_list n =
  if n = 0 then []
  else n :: build_list (n - 1)

let rec fill_list f n =
  if n = 0 then []
  else f () :: fill_list f (n - 1)

let build_fill n
(*@ ex r; build_list(n, r) @*)
= let counter =
    let x = ref 0 in
    fun () ->
      let r = !x in
      x := !x + 1;
      r
  in
  fill_list counter n