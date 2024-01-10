(* https://github.com/EmilyOng/AlgebraicEffect/blob/EmilyOng/examples/src/examples/all.ml *)

(* https://github.com/FabianWolff/closure-examples/blob/master/all.rs *)

external all : int list -> (int -> bool) -> bool = "all.Extras.all"

(* @ pure all : int list -> (int -> bool) -> bool @*)

let rec all xs pred
= match xs with
| [] -> true
| x :: xs' -> pred x && all xs' pred

(*@
  lemma all_all_false xs p =
   all(xs, p, res) ==> ens res=all(xs, p)
@*)

(* Unlike pure length, this is not provable because p on the left may have effects *)
