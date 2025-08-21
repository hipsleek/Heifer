let rec concat_option = function
  | [] -> []
  | None :: os -> concat_option os
  | Some x :: os -> x :: concat_option os


module Syntax = struct
  let ( let* ) = Option.bind
  let ( let+ ) a f = Option.map f a
end
