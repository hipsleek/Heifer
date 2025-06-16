
  $ . ../utility.sh

$ check ../examples/calls.ml
ALL OK!

$ check ../examples/compose.ml
ALL OK!

$ check ../examples/applyN.ml
ALL OK!

$ check ../examples/map.ml
ALL OK!

$ check ../examples/length.ml
ALL OK!

$ check ../examples/closure.ml
ALL OK!

  $ check ../examples/pure.ml
  ALL OK!

  $ check ../examples/fold.ml
  ALL OK!

$ check ../examples/iter.ml
ALL OK!

$ check ../examples/exception.ml
ALL OK!

$ check_why3_only ../prusti/all.ml
ALL OK!

$ check ../prusti/blameassgn.ml
ALL OK!

$ check ../prusti/counter.ml
ALL OK!

$ check ../prusti/cl_returned.ml
ALL OK!

$ check ../prusti/repeat_with_n.ml
ALL OK!

$ check_why3_only ../examples/length_pure.ml
ALL OK!

This does not work yet

$ check ../examples/all.ml
ALL OK!
