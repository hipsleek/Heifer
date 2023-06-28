
  $ function entail_results { grep 'Function\|Entail.*Check\|error'; }
  $ function sanitize { grep Time; }
  $ function check { hip "$1" 2>&1 | entail_results | ./check.py; }
  $ function results { hip "$1" 2>&1 | entail_results; }
  $ function output { hip "$1" 2>&1 | sanitize; }

  $ check test_new_entail.ml
  ALL OK!

  $ check test_ho.ml
  ALL OK!

  $ check test_lists.ml
  ALL OK!

  $ check test_closures.ml
  ALL OK!

  $ check ../evaluation/0_heap_zero_once_twice.ml
  ALL OK!

  $ check ../evaluation/1_heap_zero_once_twice.ml
  ALL OK!

  $ check ../evaluation/2_heap_zero_once_twice.ml
  ALL OK!

  $ check ../evaluation/3_nestedHandlers.ml
  ALL OK!

  $ check ../evaluation/4_memory_cell.ml
  ALL OK!

  $ check ../evaluation/5_memory_cell.ml
  ALL OK!

  $ check ../evaluation/6_memory_cell_mix_handler.ml
  ALL OK!

  $ check ../evaluation/7_memory_cell_mix_handler.ml
  ALL OK!

  $ check ../evaluation/8_memory_cell_nested.ml
  ALL OK!

  $ check ../evaluation/9_memory_cell_nested.ml
  ALL OK!

  $ check ../evaluation/10_memory_cell_nested.ml
  ALL OK!

  $ check ../evaluation/11_exchange.ml
  ALL OK!

  $ check ../evaluation/12_two_pointers.ml
  ALL OK!

  $ check ../examples/calls.ml
  ALL OK!

  $ check ../examples/compose.ml
  ALL OK!

  $ check ../examples/applyN.ml
  ALL OK!

  $ check ../examples/map.ml
  ALL OK!

  $ check ../examples/closure.ml
  ALL OK!

  $ check ../examples/fold.ml
  ALL OK!

  $ check ../examples/iter.ml
  ALL OK!

This example is very slow

$ check ../examples/all.ml
ALL OK!
