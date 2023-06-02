
  $ function entail_results { grep 'Function\|Entail.*Check'; }
  $ function sanitize { grep Time; }
  $ function check { hip "$1" 2>&1 | entail_results | ./check.py; }
  $ function results { hip "$1" 2>&1 | entail_results; }
  $ function output { hip "$1" 2>&1 | sanitize; }

  $ check test_new_entail.ml
  ALL OK!

  $ check test_ho.ml
  ALL OK!

  $ results ../evaluation/0_heap_zero_once_twice.ml
  ========== Function: test ==========
  [Entail  Check] true
  ========== Function: main_aux ==========
  [Entail  Check] true

  $ results ../evaluation/1_heap_zero_once_twice.ml
  ========== Function: test ==========
  [Entail  Check] true
  ========== Function: main_aux ==========
  [Entail  Check] true

  $ results ../evaluation/2_heap_zero_once_twice.ml
  ========== Function: test ==========
  [Entail  Check] true
  ========== Function: main_aux ==========
  [Entail  Check] false

  $ results ../evaluation/3_nestedHandlers.ml
  ========== Function: foo ==========
  [Entail  Check] true
  ========== Function: bar ==========
  [Entail  Check] true
  ========== Function: baz ==========
  [Entail  Check] true

  $ results ../evaluation/4_memory_cell.ml
  ========== Function: read ==========
  [Entail  Check] true
  ========== Function: write ==========
  [Entail  Check] true
  ========== Function: read_handler ==========
  [Entail  Check] true
  ========== Function: write_handler ==========
  [Entail  Check] true

  $ results ../evaluation/5_memory_cell.ml
  ========== Function: read ==========
  [Entail  Check] true
  ========== Function: write ==========
  [Entail  Check] true
  ========== Function: read_handler ==========
  [Entail  Check] true
  ========== Function: write_handler ==========
  [Entail  Check] true

  $ results ../evaluation/6_memory_cell_mix_handler.ml
  ========== Function: read ==========
  [Entail  Check] true
  ========== Function: write ==========
  [Entail  Check] true
  ========== Function: test1 ==========
  [Entail  Check] false
  ========== Function: test ==========
  [Entail  Check] true
  ========== Function: handler ==========
  [Entail  Check] true
  ========== Function: handler1 ==========
  [Entail  Check] true

  $ results ../evaluation/7_memory_cell_mix_handler.ml
  ========== Function: read ==========
  [Entail  Check] true
  ========== Function: write ==========
  [Entail  Check] true
  ========== Function: test ==========
  [Entail  Check] true
  ========== Function: handler ==========
  [Entail  Check] true

  $ results ../evaluation/8_memory_cell_nested.ml
  ========== Function: read ==========
  [Entail  Check] true
  ========== Function: write ==========
  [Entail  Check] true
  ========== Function: client ==========
  [Entail  Check] true
  ========== Function: handler1 ==========
  [Entail  Check] true
  ========== Function: handler2 ==========
  [Entail  Check] true

  $ results ../evaluation/9_memory_cell_nested.ml
  ========== Function: read ==========
  [Entail  Check] true
  ========== Function: write ==========
  [Entail  Check] true
  ========== Function: client ==========
  [Entail  Check] true
  ========== Function: handler1 ==========
  [Entail  Check] true
  ========== Function: handler2 ==========
  [Entail  Check] true

  $ results ../evaluation/10_memory_cell_nested.ml
  ========== Function: read ==========
  [Entail  Check] true
  ========== Function: write ==========
  [Entail  Check] true
  ========== Function: test ==========
  [Entail  Check] true
  ========== Function: write_handler ==========
  [Entail  Check] true
  ========== Function: read_handler ==========
  [Entail  Check] true

  $ results ../evaluation/11_exchange.ml
  ========== Function: exchange ==========
  [Entail  Check] true
  ========== Function: exc_hanlder ==========
  [Entail  Check] true
  ========== Function: main ==========
  [Entail  Check] true

  $ results ../evaluation/12_two_pointers.ml
  ========== Function: two_locations ==========
  [Entail  Check] true

  $ results ../examples/compose.ml
  ========== Function: compose ==========
  [Entail  Check] true
  ========== Function: f ==========
  [Entail  Check] true
  ========== Function: g ==========
  [Entail  Check] true
  ========== Function: caller1 ==========
  [Entail  Check] true
  ========== Function: caller2 ==========
  [Entail  Check] true

  $ results ../examples/applyN.ml
  ========== Function: applyN_unfolded ==========
  [Entail  Check] true
  ========== Function: applyN ==========
  ========== Function: incr ==========
  ========== Function: sum ==========
  [Entail  Check] true
  ========== Function: incr2 ==========
  ========== Function: sum2 ==========
  [Entail  Check] true
  ========== Function: summary ==========
  [Entail  Check] true
