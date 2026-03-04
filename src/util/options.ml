module Monad = struct
  let pure = Option.some
  let ( let+ ) opt f = Option.map f opt
  let ( let* ) = Option.bind
end

let guard b = if b then Some () else None

let filter f opt =
  match opt with
  | Some x when f x -> opt
  | _ -> None
