  $ . ../utility.sh
  $ check exists.ml
                 foldr: true
                exists: true
             has_solid: true
          exists_solid: true
  exists_striped_false: false (expected)
  ALL OK!
  $ check inductive_int.ml
                  plus: true
              add_zero: true
            add_zero_2: true
  ALL OK!
  $ check traffic_light.ml
                  step: true
                    id: true
           triple_step: true
     double_step_false: false (expected)
  ALL OK!
