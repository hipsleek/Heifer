  $ . ../utility.sh
  $ check exists.ml
                 foldr: true
                exists: true
             has_solid: true
          exists_solid: true
  exists_striped_false: false (expected)
         no_solids_aux: true
             no_solids: true
  ALL OK!
  $ check inductive_int.ml
                  plus: true
              add_zero: true
                  pred: true
                    id: true
  ALL OK!
  $ check traffic_light.ml
                  step: true
                    id: true
           triple_step: true
     double_step_false: false (expected)
  ALL OK!
