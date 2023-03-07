
  $ hip parse_test.ml 2>&1 | grep parsed
  parsed: ex x ret z u; Norm(x->0, ()); Label(emp, , ret); req x->z; Norm(x->z + 1, ()); req x->1; Norm(x->1, ())
  parsed: ex v; req x->1*y->2; Norm(z->3, w); Eff(z->3, v, u, r)

| ./sanitize.sh
$ hip files_paper.ml | grep Result
