
(*
   
nth(xs,n,r) =
 ens xs=x:xs'/\n=0/\res=x
 \/ ens xs=x:xs'/\n>0;nth(xs',n-1,res))
 \/ ens n<0; Failure()
 \/ ens xs=[]/\n>0; Invalid_argument()

*)

(*

ex v3; Invalid_argument((n<0)=true, (), v3); Norm(res=v3)
\/
ex v18 v20; ens (n<0)=false/\v20=lambda(\l n v17 -> ex v8; Failure(is_nil(l)=true, (), v8); Norm(v17=v8)); v20(l, n, v18); Norm(res=v18)

   *)

let nth l n =
  if n < 0 then perform Invalid_argument else
  let rec nth_aux l n =
    match l with
    | [] -> perform Failure
    | a::l -> if n = 0 then a else nth_aux l (n-1)
  in nth_aux l n