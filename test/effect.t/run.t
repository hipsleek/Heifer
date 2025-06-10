
$ . ../utility.sh

$ check ../evaluation/effect_basics.ml
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

This requires the power axioms

$ check ../../benchmarks/effects/ocaml412/A_generic_count.ml
FAILED: main

$ check ../evaluation/abort.ml
ALL OK!
