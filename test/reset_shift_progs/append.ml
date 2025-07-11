let [@pure] rec append (xs : int list) (ys : int list) : int list =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys

let rec append_reset_shift_aux xs =
  match xs with
  | [] -> shift k k
  | x :: xs' -> x :: append_shift xs'

let [@spec "ens res = append(xs, ys)"] rec append_reset_shift xs ys =
  (reset (append_reset_shift_aux xs)) ys
