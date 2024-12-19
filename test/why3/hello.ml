
let test_assign ()
(*@ ens res=1 @*)
= let i = ref 0 in
  i := !i + 1;
  !i

external one : int -> int = "hello.Extras.one"

let test_one x
(*@ ens one(res)=3 @*)
= 2
