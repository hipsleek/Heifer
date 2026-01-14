module Monad = struct
  let pure = Option.some
  let ( let+ ) opt f = Option.map f opt
  let ( let* ) = Option.bind
end
