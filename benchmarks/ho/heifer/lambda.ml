

let f1 ()
(*@ ens res=(fun x r (*@ ens r=x @*) ) @*)
= let _ = () in
  fun x (*@ ens res=x @*) -> x

let f2 ()
(*@ ens res=2 @*)
= let f3 = f1 () in
  f3 2

let g f
(*@ req f <: (fun i r (*@ req i>9; ens r>=0/\r<=99 @*) );
    ens res>=0/\res<=99 @*)
= f 10

let main ()
(*@ ens res>=0/\res<=99 @*)
= g (fun x -> 1)
