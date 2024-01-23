
(* https://arxiv.org/pdf/2104.11050.pdf *)

external fib : int -> int = "fibonacci.Extras.fib"

let fib_iter n (* FIXME *)
(*@ req n>=0; ens res=fib(n) @*)
= let x = ref 0 in
  let y = ref 1 in
  let rec aux k x y
  (*@
    req x->fib(k)*y->fib(k+1)/\0<=k/\k<n;
    ens x->fib(k+1)*y->fib(k+2);
    ex r; aux(k+1,x,y,r); ens res=r

    \/ req x->fib(k)*y->fib(k+1)/\k=n;
       ens x->fib(k)*y->fib(k+1)/\res=fib(k)
  @*)
  = if k = n then !x
    else
      let tmp = !x in
      let _ = x := !y in
      let _ = y := !y + tmp in
      aux (k + 1) x y
    in
  aux 0 x y

(* let fib_main k =
  let rec fib_rec_aux n a b k
  = if k = 0 then a
    else fib_rec_aux (n + 1) b (a + b) (k - 1)
  in
  fib_rec_aux 0 0 1 k *)
