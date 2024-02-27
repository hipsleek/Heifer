effect Flip : bool

let rec tossNtimeRight n 
(*@ req n>=1; ex r; Flip(n=1, r) ; Norm(res=r, res) \/ 
    req n>=1; ex r1; Flip(emp, r1); ex r2; tossNtimeRight(n-1, r2); Norm(n>1, r1&&r2)  @*)
= if n==1 then 
    perform Flip
  else 
    let r1 = perform Flip in 
    let r2 = tossNtimeRight (n-1) 
    in r1 && r2

let rec tossNtimeLeft n 
(*@ req n>=1; ex r; Flip(n=1, r) ; Norm(res=r, res) \/ 
    req n>=1; ex r1; tossNtimeLeft(n-1, r1); ex r2; Flip(emp, r2);  Norm(n>1, r1&&r2)  @*)
= if n==1 then 
    perform Flip
  else 
    let r1 = tossNtimeLeft (n-1)  in 
    let r2 = perform Flip
    in r1 && r2


  (*  shallow try ex r; req n>0; tossNtimeLeft(n,r) 
      # ex acc' r'; ens acc'= acc/\r; helper (m, acc', r' )
      catch 
  =  ex w1 r1; req counter->w1; ens counter->w1+1; helper (n-1+m, acc, r1);
     ex w2 r2; req counter->w2; ens counter->w2+1; helper (n-1+m, false, r2); 
     Norm(res=r1, res)
  *)

let tossHandlerTail counter n 
(*@ ex w; req counter->w /\ n>=1; Norm (counter->w+2 /\ n=1 ,1)  \/ 
    ex w1 r1; req counter->w1/\ n>=1 ; ens counter->w1+1;  tossNtimeRight(n-1, r1); 
    ex w2 r2; req counter->w2 ; ens counter->w2+1; tossNtimeRight(n-1, r2); 
    Norm(n>1 /\ r1=true, 1) \/
    ex w1 r1; req counter->w1/\ n>=1 ; ens counter->w1+1;  tossNtimeRight(n-1, r1); 
    ex w2 r2; req counter->w2 ; ens counter->w2+1; tossNtimeRight(n-1, r2); 
    Norm(n>1 /\ r1=false, 0) 
@*)
= match tossNtimeLeft n with 
  (* try-catch lemma defined here *)
  (*@  shallow try ex r; req n>0; tossNtimeLeft(n,r) 
      # ex acc1 r1; ens acc1=(acc&&r); helper (m, acc1, r1)
      catch 
  =  ex w1 acc1 i1; req counter->w1; ens counter->w1+1 /\ i1=(n-1)+m; helper (i1, acc, acc1);
     ex w2 acc2 i2; req counter->w2; ens counter->w2+1/\ i2=(n-1)+m; helper (i2, false, acc2); 
     Norm(res=acc1, res) 
  @*) 
  | x -> if x 
         then 1 
         else 0     

  | effect Flip k ->
      counter := !counter + 1;            (* increase the counter *)
      let res1 = continue (Obj.clone_continuation k) true in         (* resume with true     *)
      counter := !counter + 1;            (* increase the counter *)
      let res2 = continue k false in      (* resume with false    *)
      res1 + res2                         (* gather the results   *)

