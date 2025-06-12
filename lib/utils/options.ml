let rec concat_option = function
  | [] -> []
  | None :: os -> concat_option os
  | Some x :: os -> x :: concat_option os
