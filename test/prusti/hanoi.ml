
(* https://github.com/viperproject/prusti-dev/blob/master/prusti-tests/tests/verify_overflow/pass/rosetta/Towers_of_Hanoi_spec.rs *)

let[@pure] valid_pole (x: int): bool = x = 1 || x = 2 || x = 3

let[@pure] equals (a: int) (b: int): bool = a = b

let record_move src dest
(*@ req valid_pole(src)=true/\valid_pole(dest)=true/\equals(src, dest)=false @*)
= ()

let rec move n src dest via =
  if n > 0 then
    move (n - 1) src via dest;
    record_move src dest;
    move (n - 1) via dest src

let move_spec n src dest via
(*@
  req n>=0/\valid_pole(src)=true/\valid_pole(dest)=true/\valid_pole(via)=true;
  req equals(src,dest)=false/\equals(dest,via)=false/\equals(via,src)=false;
  ex r; move(n,src,dest,via,r);
  ens res=r
@*)
= move n src dest via
