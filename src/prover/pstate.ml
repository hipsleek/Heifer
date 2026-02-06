open Util

type t = Pctx.t list

let destruct xs = List.map Lists.singleton xs

let focus = function
  | [] -> ([], [])
  | s :: ss -> ([s], ss)

let is_empty = List.is_empty

let append = List.append

let pp ppf s =
  match s with
  | [] -> Fmt.pf ppf "no more goals"
  | g :: gs ->
      Fmt.pf ppf "@[<v>@,%a" Pctx.pp g;
      (match List.length gs with
      | 0 -> ()
      | n -> Fmt.pf ppf "@,(%d more goals)" n);
      Fmt.pf ppf "@,@]"
