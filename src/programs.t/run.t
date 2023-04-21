
  $ hip test_new_entail.ml 2>&1 | grep 'Function\|Entail' | grep true
  ========== Function: test10_true ==========
  [Entail  Check] true
  ========== Function: test6_true ==========
  [Entail  Check] true
  ========== Function: test9_true ==========
  [Entail  Check] true
  ========== Function: test4_true ==========
  [Entail  Check] true
  ========== Function: test5_true ==========
  [Entail  Check] true
  ========== Function: test6_true ==========
  [Entail  Check] true
  ========== Function: test11_true ==========
  [Entail  Check] true
  ========== Function: test19_true ==========
  ========== Function: test0_true ==========
  [Entail  Check] true
  ========== Function: test13_true ==========
  [Entail  Check] true
  ========== Function: test18_true ==========
  [Entail  Check] true
  ========== Function: test20_true ==========
  [Entail  Check] true
  ========== Function: test15_true ==========
  ========== Function: test17_true ==========

  $ hip test_new_entail.ml 2>&1 | grep 'Function\|Entail' | grep false
  ========== Function: test7_false ==========
  [Entail  Check] false
  ========== Function: test8_false ==========
  [Entail  Check] false
  ========== Function: test12_false ==========
  [Entail  Check] false
  [Entail  Check] false
  ========== Function: test1_false ==========
  [Entail  Check] false
  ========== Function: test2_false ==========
  [Entail  Check] false
  ========== Function: test3_false ==========
  [Entail  Check] false
  [Entail  Check] false
  ========== Function: test14_false ==========
  [Entail  Check] false
  ========== Function: test16_false ==========
  [Entail  Check] false
  [Entail  Check] false

  $ hip test_new_entail.ml 2>&1 | ./sanitize.sh
  T=>T // norm pre
  /\ T=>T // norm post
  /\ 0=0 // norm res eq
  z3: valid
  
  
  ========== Function: test10_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ===========================================
  
  T=>T // norm pre
  /\ T=>T // norm post
  /\ 0=0 // norm res eq
  z3: valid
  
  
  ========== Function: test6_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ==========================================
  
  T=>T // norm pre
  /\ T=>T // norm post
  /\ 0=j // norm res eq
  z3: not valid
  
  
  ========== Function: test7_false ==========
  [Specification] Norm(emp, j)
  [Normed   Spec] Norm(emp, j)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  ===========================================
  
  T=>T // norm pre
  /\ T=>T // norm post
  /\ 0=k // norm res eq
  z3: not valid
  
  
  ========== Function: test8_false ==========
  [Specification] Norm(emp, k)
  [Normed   Spec] Norm(emp, k)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  ===========================================
  
  ex j. T=>T // norm pre
  /\ T=>T // norm post
  /\ 0=j // norm res eq
  z3: valid
  
  
  ========== Function: test9_true ==========
  [Specification] ex j; Norm(emp, j)
  [Normed   Spec] ex j; Norm(emp, j)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 i. T=>T // norm pre
  /\ T=>0=0 // norm post
  /\ f0=i // norm res eq
  z3: valid
  
  
  ========== Function: test4_true ==========
  [Specification] ex i; Norm(i->0, i)
  [Normed   Spec] ex i; Norm(i->0, i)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, f0)
  [Normed   Post] ex f0; Norm(f0->0, f0)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 i_1 i. T=>T // norm pre
  /\ i_1=0=>0=i_1 // norm post
  /\ i_1+1=1 // norm res eq
  z3: valid
  
  
  ========== Function: test5_true ==========
  [Specification] ex i; Norm(i->0, 1)
  [Normed   Spec] ex i; Norm(i->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+1)
  [Normed   Post] ex f0 i_1; Norm(f0->i_1 /\ i_1=0, i_1+1)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 i_1 f2 i_3 i. T=>i_1=f2/\i_1+1=i_3 // norm pre
  /\ i_1=0/\f2=i_1/\i_3=i_1+1=>1=i_3 // norm post
  /\ i_3=1 // norm res eq
  z3: valid
  
  
  ========== Function: test6_true ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+1); ex f2; req f0->f2; Norm(f0->i_1+1, ()); ex i_3; req f0->i_3; Norm(f0->i_3, i_3)
  [Normed   Post] ex f0 i_1 f2 i_3; req i_1=f2/\i_1+1=i_3; Norm(f0->i_3 /\ i_1=0/\f2=i_1/\i_3=i_1+1, i_3)
  
  [Entail  Check] true
  ==========================================
  
  ex res_0. T=>T // norm pre
  /\ T=>T // norm post
  /\ res_0=() // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_0=() // post stage 0
  z3: valid
  
  
  ========== Function: test11_true ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); Norm(emp, ())
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, res_0)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, res_0)
  
  [Entail  Check] true
  ===========================================
  
  ex res_0. T=>T // norm pre
  /\ T=>T // norm post
  /\ 1=() // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_0=() // post stage 0
  z3: not valid
  
  
  ========== Function: test12_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); Norm(emp, ())
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, 1)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, 1)
  
  [Entail  Check] false
  ============================================
  
  ex res_0 r. T=>T // norm pre
  /\ T=>T // norm post
  /\ 1=() // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_0=r // post stage 0
  z3: not valid
  
  
  ========== Function: test19_true ==========
  [Specification] ex r; Eff(emp, [], r)
  [Normed   Spec] ex r; Eff(emp, [], r); Norm(emp, ())
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, 1)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, 1)
  
  [Entail  Check] false
  ===========================================
  
  ex f0 res_1 i_2 f3 i. T=>i_2=z/\i_2=f3 // norm pre
  /\ f3=i_2=>z+1=i_2+1 // norm post
  /\ res_1=ret // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_1=ret/\0=0 // post stage 0
  z3: valid
  
  
  ========== Function: test0_true ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+1 /\ f3=i_2, res_1)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 res_1 i_2 f3 i_4 i. T=>i_2=z/\i_2=f3/\i_2+1=i_4 // norm pre
  /\ f3=i_2/\i_4=i_2+1=>z+1=i_4 // norm post
  /\ i_4=ret // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_1=ret/\0=0 // post stage 0
  z3: not valid
  
  
  ========== Function: test1_false ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); ex i_4; req f0->i_4; Norm(f0->i_4, i_4)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3 i_4; req f0->i_2 /\ i_2=f3/\i_2+1=i_4; Norm(f0->i_4 /\ f3=i_2/\i_4=i_2+1, i_4)
  
  [Entail  Check] false
  ===========================================
  
  
  ========== Function: test2_false ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); Norm(emp, res_1)
  
  [Entail  Check] false
  ===========================================
  
  ex f0 res_1 i_2 f3 i. T=>i_2=z/\i_2=f3 // norm pre
  /\ f3=i_2=>z+1=i_2+2 // norm post
  /\ res_1=ret // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_1=ret/\0=0 // post stage 0
  z3: not valid
  
  
  ========== Function: test3_false ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+2); ex f3; req f0->f3; Norm(f0->i_2+2, ()); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+2 /\ f3=i_2, res_1)
  
  [Entail  Check] false
  ===========================================
  
  ex f0 f1 a b. T=>T // norm pre
  /\ T=>0=0 // norm post
  /\ 1=1 // norm res eq
  z3: valid
  
  
  ========== Function: test13_true ==========
  [Specification] ex a b; Norm(a->0*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->0*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->1, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->1, 1)
  
  [Entail  Check] true
  ===========================================
  
  ex f0 f1 a b. T=>T // norm pre
  /\ T=>1+1=0 // norm post
  /\ 1=1 // norm res eq
  z3: not valid
  
  ex f0 f1 a b. T=>T // norm pre
  /\ T=>1+1=2 // norm post
  /\ 1=1 // norm res eq
  z3: valid
  
  
  ========== Function: test18_true ==========
  [Specification] ex a b; Norm(a->1+1*b->0, 1)
  [Normed   Spec] ex a b; Norm(a->1+1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->2, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  
  ========== Function: test20_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->2, f0); Norm(emp, 1)
  [Normed   Post] ex f0; Norm(f0->2, 1)
  
  [Entail  Check] false
  ===========================================
  
  ex f0 f1 a b. T=>T // norm pre
  /\ T=>1=0 // norm post
  /\ 1=1 // norm res eq
  z3: not valid
  
  ex f0 f1 a b. T=>T // norm pre
  /\ T=>1=1 // norm post
  /\ 1=1 // norm res eq
  z3: valid
  
  
  ========== Function: test14_false ==========
  [Specification] ex a b; Norm(a->1*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->1*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->1, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->1, 1)
  
  [Entail  Check] true
  ============================================
  
  
  ========== Function: test15_true ==========
  [Specification] req a->1; Norm(a->1, 1)
  [Normed   Spec] req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 1)
  [Normed   Post] Norm(emp, 1)
  
  [Entail  Check] false
  ===========================================
  
  ex f0 a. a>0=>T // norm pre
  /\ T=>1=0 // norm post
  /\ 1=1 // norm res eq
  z3: not valid
  
  
  ========== Function: test16_false ==========
  [Specification] ex a; req a->1; Norm(a->1, 1)
  [Normed   Spec] ex a; req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, 1)
  [Normed   Post] ex f0; Norm(f0->0, 1)
  
  [Entail  Check] false
  ============================================
  
  
  ========== Function: test17_true ==========
  [Specification] ex b; req a->1; Norm(a->1*b->0, 1)
  [Normed   Spec] ex b; req a->1; Norm(a->1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, 1)
  [Normed   Post] ex f0; Norm(f0->0, 1)
  
  [Entail  Check] false
  ===========================================
  
