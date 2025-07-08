
  $ . ../utility.sh

  $ check ../reset_shift_progs/either.ml
                either: true
                  main: true
  ALL OK!

  $ check ../reset_shift_progs/hello.ml
                 hello: true
  ALL OK!

  $ check ../reset_shift_progs/hello1.ml
                hello1: true
  ALL OK!

  $ check ../reset_shift_progs/hello41.ml
               hello41: true
  ALL OK!

  $ check ../reset_shift_progs/hello_printf.ml
               get_int: true
            get_string: true
      hello_printf_int: true
  hello_printf_string1: true
          hello_printf: true
    hello_printf_false: false (expected)
  ALL OK!

  $ check ../reset_shift_progs/list_identity.ml
     list_identity_aux: true
         list_identity: false
            empty_list: true
        singleton_list: false
  [1]

  $ check ../reset_shift_progs/list_map.ml
                   map: true
   map_shift_reset_aux: true
       map_shift_reset: true
                    id: true
                  succ: true
                map_id: true
            empty_list: true
        singleton_list: false
         empty_list_v1: true
     singleton_list_v1: false
  [1]

  $ check ../reset_shift_progs/state_monad.ml
                   get: true
                  tick: true
             run_state: true
                  main: true
                 main1: true
  ALL OK!

  $ check ../reset_shift_progs/translate.ml
          hello_lambda: true
          hello_string: true
     hello_string_conc: true
           undelimited: true
                 hello: true
                hello1: true
                hello3: true
               hello41: true
                hello4: true
                hello5: true
                hello6: true
                hello7: true
             hello_eta: true
                hello8: true
          hello_printf: true
             hello_s2i: true
               get_int: true
            get_string: true
      hello_printf_int: true
  hello_printf_string1: true
          hello_printf: true
    hello_printf_false: false (expected)
  ALL OK!
