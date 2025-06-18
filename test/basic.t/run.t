
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
          test23_false: true
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
                test24: false
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
  ALL OK!

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
  ALL OK!

  $ check test_lists.ml
                   map: true
                  incr: true
         map_inc_false: false (expected)
            test1_true: false
           test2_false: false (expected)
            test3_true: false
            test4_true: false
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
                    f1: false
                    f2: false
                    f3: false
                    f4: false
              f5_false: false (expected)
                    f6: false
                    f7: false
                 apply: true
                    f8: false
  ALL OK!
