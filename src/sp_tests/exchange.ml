effect Exchange : (int ref * int * int) -> unit

let client () 
(*@ requires emp  @*)
(*@ ensures {i->0}.Exchange(i, 0, 5).[i=5] @*)
= 
  let x, x' = 0, 5 in 
  let (i:int ref) = Sys.opaque_identity (ref x) in
  perform (Exchange (i, x, x'));
  Printf.printf "i = %d\n%!" !i;
  assert (!i = x')
   
let main 
=
  match client () with
  | v -> ()
  | effect (Exchange (j, v, v')) k -> 
    assert (!j = v);
    j := v'; 
    (continue k ()); 

(*      
For Exchange: 
{i->0}.Exchange(i, 0, 5).[i=5] 
    currenct effects       continuation k                statck     /\ heap     /\ assertion 
    --------------------------------------------------------------------------------
    {i->0}                 Exchange(i, 0, 5).[i=5]                     i=0
    Exchange(i, 0, 5)      [j=v].{j->v'}.[i=5]            v=0,v'=5  /\ j=i=0   
    [j=v]                  {j->v'}.[i=5]                  v=0,v'=5  /\ j=i=0    /\  true 
    {j->v'}                [i=5]                          v=0,v'=5  /\ j=i=5   
    [i=5]                  emp                            v=0,v'=5  /\ j=i=5    /\  true 
*)