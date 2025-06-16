
  $ . ../utility.sh

$ check ../examples/calls.ml
ALL OK!

$ check ../examples/compose.ml
ALL OK!

$ check ../examples/applyN.ml
ALL OK!

  $ check ../examples/map.ml
                   map: true
                    id: true
                map_id: true
                  succ: true
      map_not_id_false: false (expected)
             succ_list: true
              map_succ: true
           thrice_list: true
            map_thrice: true
  ALL OK!

$ check ../examples/length.ml
ALL OK!

$ check ../examples/closure.ml
ALL OK!

  $ check ../examples/pure.ml
                 hello: true
            pure_hello: true
  ALL OK!

  $ check ../examples/fold.ml
                length: true
                   sum: true
                 foldr: true
             foldr_sum: true
          foldr_length: true
                 foldl: true
             foldl_sum: true
          foldl_length: true
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
