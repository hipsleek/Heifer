module Monad = struct
  let pure = Option.some
  let ( let+ ) opt f = Option.map f opt
  let ( let* ) = Option.bind
end

let filter f opt =
  match opt with
  | Some x when f x -> opt
  | _ -> None
