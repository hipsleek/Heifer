let pow10 =
  let rec go r k =
    if k <= 0 then r
    else go (10 * r) (k - 1)
  in
  go 1

let log10 =
  let rec go r n =
    if n <= 0 then r
    else go (r + 1) (n / 10)
  in
  go 0
