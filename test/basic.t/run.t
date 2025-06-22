
  $ . ../utility.sh

  $ check test_new_entail.ml
                test10: true
              test10_s: true
                 test6: true
           test7_false: false (expected)
           test8_false: false (expected)
                 test9: false
                 test4: true
                 test5: true
                test61: true
          test23_false: false (expected)
                test13: true
                test18: true
                test20: false
                test21: false
                test22: false
          test14_false: false (expected)
                test15: true
                test16: false
                test17: false
                    f1: true
                test24: true
                    fa: true
                test26: true
               if_disj: true
                if_let: true
                  foo1: true
                  foo2: true
                  goo1: false
                  goo2: false
           call_f_in_g: true
              call_ret: true
     test_non_rec_pred: true
             test_read: true
  [1]

  $ check test_ho.ml
            test1_true: false
           test1_false: false (expected)
            test2_true: false
           test5_false: false (expected)
            test3_true: false
            test4_true: false
            test6_true: false
           test7_false: false (expected)
          compose_true: false
   compose_exists_true: false
  [1]

  $ check test_lists.ml
                   map: true
                  incr: true
         map_inc_false: false (expected)
            test1_true: true
           test2_false: false (expected)
            test3_true: true
            test4_true: true
  ALL OK!

  $ check_why3_only test_lambda.ml
  ALL OK!

  $ check test_unfolding.ml
                 test1: true
                    f2: true
                 test2: true
                 test3: true
  ALL OK!

  $ check test_closures.ml
                    f1: true
                    f2: true
                    f3: true
                    f4: true
              f5_false: false (expected)
                    f6: true
                    f7: true
                 apply: true
                    f8: true
  ALL OK!
