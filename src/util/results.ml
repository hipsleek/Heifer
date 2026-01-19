let choice r1 r2 =
  match r1 with
  | Ok _ -> r1
  | Error _ -> r2

module Monad = struct
  let pure = Result.ok
  let ( let+ ) r f = Result.map f r
  let ( let* ) = Result.bind
end
