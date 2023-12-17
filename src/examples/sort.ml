
let rec partition xs pivot =
  match xs with
  | [] -> ([], [])
  | y :: ys ->
    let less_than, greater_than = partition ys pivot in
      if y <= pivot then (y :: less_than, greater_than)
      else (less_than, y :: greater_than)

let rec quicksort xs
= match xs with
  | [] -> []
  | y :: ys ->
    (* Choose the head as a pivot *)
    let lesser_than_equal, greater_than = partition ys y in
    quicksort lesser_than_equal @ y :: (quicksort greater_than)
