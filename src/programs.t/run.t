
  $ hip test_new_entail.ml 2>&1 | grep 'Function\|Entail.*Check' | ./check.py
  TESTS FAILED
  ========== Function: test12_false ==========
  ========== Function: test14_false ==========

  $ hip test_new_entail.ml 2>&1 | ./sanitize.sh
  T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ 0=0 // norm res eq: 0 = 0
  z3: valid
  
  
  ========== Function: test10_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ===========================================
  
  T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ 0=0 // norm res eq: 0 = 0
  z3: valid
  
  
  ========== Function: test6_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ==========================================
  
  T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ 0=j // norm res eq: 0 = j
  z3: not valid
  
  
  ========== Function: test7_false ==========
  [Specification] Norm(emp, j)
  [Normed   Spec] Norm(emp, j)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  ===========================================
  
  T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ 0=k // norm res eq: 0 = k
  z3: not valid
  
  
  ========== Function: test8_false ==========
  [Specification] Norm(emp, k)
  [Normed   Spec] Norm(emp, k)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  ===========================================
  
  ex j. T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ 0=j // norm res eq: 0 = j
  z3: valid
  
  
  ========== Function: test9_true ==========
  [Specification] ex j; Norm(emp, j)
  [Normed   Spec] ex j; Norm(emp, j)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 i. T=>T // norm pre: emp |= emp
  /\ T=>0=0 // norm post: f0->0 |= i->0
  /\ f0=i // norm res eq: f0 = i
  z3: valid
  
  
  ========== Function: test4_true ==========
  [Specification] ex i; Norm(i->0, i)
  [Normed   Spec] ex i; Norm(i->0, i)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, f0)
  [Normed   Post] ex f0; Norm(f0->0, f0)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 i_1 i. T=>T // norm pre: emp |= emp
  /\ i_1=0=>0=i_1 // norm post: f0->i_1 /\ i_1=0 |= i->0
  /\ i_1+1=1 // norm res eq: i_1+1 = 1
  z3: valid
  
  
  ========== Function: test5_true ==========
  [Specification] ex i; Norm(i->0, 1)
  [Normed   Spec] ex i; Norm(i->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+1)
  [Normed   Post] ex f0 i_1; Norm(f0->i_1 /\ i_1=0, i_1+1)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 i_1 f2 i_3 i. T=>i_1=f2/\i_1+1=i_3 // norm pre: emp |= i_1=f2/\i_1+1=i_3
  /\ i_1=0/\f2=i_1/\i_3=i_1+1=>1=i_3 // norm post: f0->i_3 /\ i_1=0/\f2=i_1/\i_3=i_1+1 |= i->1
  /\ i_3=1 // norm res eq: i_3 = 1
  z3: valid
  
  
  ========== Function: test6_true ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+1); ex f2; req f0->f2; Norm(f0->i_1+1, ()); ex i_3; req f0->i_3; Norm(f0->i_3, i_3)
  [Normed   Post] ex f0 i_1 f2 i_3; req i_1=f2/\i_1+1=i_3; Norm(f0->i_3 /\ i_1=0/\f2=i_1/\i_3=i_1+1, i_3)
  
  [Entail  Check] true
  ==========================================
  
  ex res_0 n_8. T=>T // pre stage 0: emp |= emp
  /\ T=>res_0=() // post stage 0: emp |= emp
  /\ T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ res_0=n_8 // norm res eq: res_0 = n_8
  z3: valid
  
  
  ========== Function: test11_true ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); ex n_2; Norm(emp, n_2)
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, res_0)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, res_0)
  
  [Entail  Check] true
  ===========================================
  
  ex res_0 n_8. T=>T // pre stage 0: emp |= emp
  /\ T=>res_0=() // post stage 0: emp |= emp
  /\ T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ 1=n_8 // norm res eq: 1 = n_8
  z3: valid
  
  
  ========== Function: test12_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); ex n_2; Norm(emp, n_2)
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, 1)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, 1)
  
  [Entail  Check] true
  ============================================
  
  ex res_0 r n_8. T=>T // pre stage 0: emp |= emp
  /\ T=>res_0=r // post stage 0: emp |= emp
  /\ T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ 1=n_8 // norm res eq: 1 = n_8
  z3: valid
  
  
  ========== Function: test19_true ==========
  [Specification] ex r; Eff(emp, [], r)
  [Normed   Spec] ex r; Eff(emp, [], r); ex n_2; Norm(emp, n_2)
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, 1)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, 1)
  
  [Entail  Check] true
  ===========================================
  
  ex f0 res_1 i_2 f3 i ret. T=>T // pre stage 0: emp |= emp
  /\ T=>res_1=ret/\0=0 // post stage 0: f0->0 |= i->0
  /\ T=>i_2=z/\i_2=f3 // norm pre: i->z |= f0->i_2 /\ i_2=f3
  /\ f3=i_2=>z+1=i_2+1 // norm post: f0->i_2+1 /\ f3=i_2 |= i->z+1
  /\ res_1=ret // norm res eq: res_1 = ret
  z3: valid
  
  
  ========== Function: test21_true ==========
  [Specification] ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+1 /\ f3=i_2, res_1)
  
  [Entail  Check] true
  ===========================================
  
  ex f0 res_1 i_2 f3 i. T=>T // pre stage 0: emp |= emp
  /\ T=>res_1=ret/\0=0 // post stage 0: f0->0 |= i->0
  /\ T=>i_2=z/\i_2=f3 // norm pre: i->z |= f0->i_2 /\ i_2=f3
  /\ f3=i_2=>z+1=i_2+1 // norm post: f0->i_2+1 /\ f3=i_2 |= i->z+1
  /\ res_1=ret // norm res eq: res_1 = ret
  z3: valid
  
  
  ========== Function: test0_true ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+1 /\ f3=i_2, res_1)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 res_1 i_2 f3 i_4 i. T=>T // pre stage 0: emp |= emp
  /\ T=>res_1=ret/\0=0 // post stage 0: f0->0 |= i->0
  /\ T=>i_2=z/\i_2=f3/\i_2+1=i_4 // norm pre: i->z |= f0->i_2 /\ i_2=f3/\i_2+1=i_4
  /\ f3=i_2/\i_4=i_2+1=>z+1=i_4 // norm post: f0->i_4 /\ f3=i_2/\i_4=i_2+1 |= i->z+1
  /\ i_4=ret // norm res eq: i_4 = ret
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
  
  ex f0 res_1 i_2 f3 i. T=>T // pre stage 0: emp |= emp
  /\ T=>res_1=ret/\0=0 // post stage 0: f0->0 |= i->0
  /\ T=>i_2=z/\i_2=f3 // norm pre: i->z |= f0->i_2 /\ i_2=f3
  /\ f3=i_2=>z+1=i_2+2 // norm post: f0->i_2+2 /\ f3=i_2 |= i->z+1
  /\ res_1=ret // norm res eq: res_1 = ret
  z3: not valid
  
  
  ========== Function: test3_false ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+2); ex f3; req f0->f3; Norm(f0->i_2+2, ()); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+2 /\ f3=i_2, res_1)
  
  [Entail  Check] false
  ===========================================
  
  ex f0 f1 a b. T=>T // norm pre: emp |= emp
  /\ T=>0=0 // norm post: f0->0*f1->1 |= a->0*b->1
  /\ 1=1 // norm res eq: 1 = 1
  z3: valid
  
  
  ========== Function: test13_true ==========
  [Specification] ex a b; Norm(a->0*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->0*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->1, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->1, 1)
  
  [Entail  Check] true
  ===========================================
  
  ex f0 f1 a b. T=>T // norm pre: emp |= emp
  /\ T=>1+1=0 // norm post: f0->0*f1->2 |= a->1+1*b->0
  /\ 1=1 // norm res eq: 1 = 1
  z3: not valid
  
  ex f0 f1 a b. T=>T // norm pre: emp |= emp
  /\ T=>1+1=2 // norm post: f0->0*f1->2 |= a->1+1*b->0
  /\ 1=1 // norm res eq: 1 = 1
  z3: valid
  
  
  ========== Function: test18_true ==========
  [Specification] ex a b; Norm(a->1+1*b->0, 1)
  [Normed   Spec] ex a b; Norm(a->1+1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->2, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  ex f0 b. T=>T // norm pre: i->1 |= i->1
  /\ T=>T // norm post: i->1*f0->2 |= i->1*b->2
  /\ 1=1 // norm res eq: 1 = 1
  z3: valid
  
  
  ========== Function: test20_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); req i->1; Norm(i->1, ()); ex f0; Norm(f0->2, f0); Norm(emp, 1)
  [Normed   Post] ex f0; req i->1; Norm(i->1*f0->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  ex f0 b. T=>T // norm pre: i->1 |= i->1
  /\ T=>T // norm post: i->1*f0->2 |= i->1*b->2
  /\ 1=1 // norm res eq: 1 = 1
  z3: valid
  
  
  ========== Function: test21_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); req i->1; Norm(i->1, ()); ex f0; Norm(f0->2, f0); req f0->2; Norm(f0->2, ()); Norm(emp, 1)
  [Normed   Post] ex f0; req i->1; Norm(i->1*f0->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  ex f0 j_1 i a. T=>T // norm pre: emp |= emp
  /\ j_1=2=>a=j_1 // norm post: f0->j_1 /\ j_1=2 |= i->a
  /\ ()=() // norm res eq: () = ()
  z3: valid
  
  
  ========== Function: test22_true ==========
  [Specification] ex i a; Norm(i->a, ())
  [Normed   Spec] ex i a; Norm(i->a, ())
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->2, f0); ex j_1; req f0->j_1; Norm(f0->j_1, j_1); req f0->j_1; Norm(f0->j_1, ())
  [Normed   Post] ex f0 j_1; Norm(f0->j_1 /\ j_1=2, ())
  
  [Entail  Check] true
  ===========================================
  
  ex f0 f1 a b. T=>T // norm pre: emp |= emp
  /\ T=>1=0 // norm post: f0->0*f1->1 |= a->1*b->1
  /\ 1=1 // norm res eq: 1 = 1
  z3: not valid
  
  ex f0 f1 a b. T=>T // norm pre: emp |= emp
  /\ T=>1=1 // norm post: f0->0*f1->1 |= a->1*b->1
  /\ 1=1 // norm res eq: 1 = 1
  z3: valid
  
  
  ========== Function: test14_false ==========
  [Specification] ex a b; Norm(a->1*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->1*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->1, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->1, 1)
  
  [Entail  Check] true
  ============================================
  
  T=>T // norm pre: a->1 |= a->1
  /\ T=>T // norm post: a->1 |= a->1
  /\ 1=1 // norm res eq: 1 = 1
  z3: valid
  
  
  ========== Function: test15_true ==========
  [Specification] req a->1; Norm(a->1, 1)
  [Normed   Spec] req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); req a->1; Norm(a->1, ()); Norm(emp, 1)
  [Normed   Post] req a->1; Norm(a->1, 1)
  
  [Entail  Check] true
  ===========================================
  
  ex f0 a. a>0=>T // norm pre: a->1 |= emp
  /\ T=>1=0 // norm post: f0->0 |= a->1
  /\ 1=1 // norm res eq: 1 = 1
  z3: not valid
  
  
  ========== Function: test16_false ==========
  [Specification] ex a; req a->1; Norm(a->1, 1)
  [Normed   Spec] ex a; req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, 1)
  [Normed   Post] ex f0; Norm(f0->0, 1)
  
  [Entail  Check] false
  ============================================
  
  ex f0 b. T=>T // norm pre: a->1 |= a->1
  /\ T=>T // norm post: a->1*f0->0 |= a->1*b->0
  /\ 1=1 // norm res eq: 1 = 1
  z3: valid
  
  
  ========== Function: test17_true ==========
  [Specification] ex b; req a->1; Norm(a->1*b->0, 1)
  [Normed   Spec] ex b; req a->1; Norm(a->1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); req a->1; Norm(a->1, ()); ex f0; Norm(f0->0, f0); Norm(emp, 1)
  [Normed   Post] ex f0; req a->1; Norm(a->1*f0->0, 1)
  
  [Entail  Check] true
  ===========================================
  

  $ hip test_ho.ml 2>&1 | grep 'Function\|Entail.*Check' | ./check.py
  ALL OK!

  $ hip test_ho.ml 2>&1 | ./sanitize.sh
  ex f0 n_6 r. T=>T // pre stage 0: emp |= emp
  /\ T=>f0=r // post stage 0: emp |= emp
  /\ T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ n_6=r // norm res eq: n_6 = r
  z3: valid
  
  
  ========== Function: test1_true ==========
  [Specification] ex r; f(emp, [1], r); Norm(emp, r)
  [Normed   Spec] ex r; f(emp, [1], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; f(emp, [1], f0)
  [Normed   Post] ex f0; f(emp, [1], f0); ex n_4; Norm(emp, n_4)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 f1 n_10 r s. T=>T // pre stage 0: emp |= emp
  /\ T=>f0=r // post stage 0: emp |= emp
  /\ T=>T // pre stage 1: emp |= emp
  /\ T=>f1=s // post stage 1: emp |= emp
  /\ T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ n_10=s // norm res eq: n_10 = s
  z3: valid
  
  
  ========== Function: test2_true ==========
  [Specification] ex r; ex s; f(emp, [1], r); g(emp, [2], s); Norm(emp, s)
  [Normed   Spec] ex r s; f(emp, [1], r); g(emp, [2], s); Norm(emp, s)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; f(emp, [1], f0); ex f1; g(emp, [1], f1)
  [Normed   Post] ex f0; f(emp, [1], f0); ex f1; g(emp, [1], f1); ex n_7; Norm(emp, n_7)
  
  [Entail  Check] true
  ==========================================
  
  ex f0 f1 n_10 r s. T=>T // pre stage 0: emp |= emp
  /\ T=>f0=r // post stage 0: emp |= emp
  /\ T=>T // pre stage 1: emp |= emp
  /\ T=>f1=s // post stage 1: emp |= emp
  /\ T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ n_10=s // norm res eq: n_10 = s
  z3: valid
  
  
  ========== Function: test3_true ==========
  [Specification] ex r; ex s; f(emp, [1], r); g(emp, [r], s); Norm(emp, s)
  [Normed   Spec] ex r s; f(emp, [1], r); g(emp, [r], s); Norm(emp, s)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; f(emp, [1], f0); ex f1; g(emp, [f0], f1)
  [Normed   Post] ex f0; f(emp, [1], f0); ex f1; g(emp, [f0], f1); ex n_7; Norm(emp, n_7)
  
  [Entail  Check] true
  ==========================================
  
  ex r_2 r. T=>T // pre stage 0: emp |= emp
  /\ T=>r_2=r // post stage 0: emp |= emp
  /\ T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ r_2=r // norm res eq: r_2 = r
  z3: valid
  
  
  ========== Function: test4_true ==========
  [Specification] ex r; test4_true(emp, [()], r); Norm(emp, r)
  [Normed   Spec] ex r; test4_true(emp, [()], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); ex r_2; test4_true(emp, [()], r_2); Norm(emp, r_2)
  [Normed   Post] ex r_2; test4_true(emp, [()], r_2); Norm(emp, r_2)
  
  [Entail  Check] true
  ==========================================
  
  T=>T // norm pre: emp |= emp
  /\ b=0=>T // norm post: b=0 |= emp
  /\ 0=0 // norm res eq: 0 = 0
  z3: valid
  
  T=>T // norm pre: emp |= emp
  /\ !b=0=>T // norm post: !b=0 |= emp
  /\ 0=0 // norm res eq: 0 = 0
  z3: valid
  
  ex r_3 r. T=>T // pre stage 0: emp |= emp
  /\ !b=0=>r_3=r // post stage 0: !b=0 |= emp
  /\ T=>T // norm pre: emp |= emp
  /\ T=>T // norm post: emp |= emp
  /\ r_3=r // norm res eq: r_3 = r
  z3: valid
  
  
  ========== Function: test5_true ==========
  [Specification] Norm(emp, 0) \/ ex r; test5_true(emp, [b; n-1], r); Norm(emp, r)
  [Normed   Spec] Norm(emp, 0) \/ ex r; test5_true(emp, [b; n-1], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=0, ()); Norm(emp, n-1); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=0, ()); Norm(emp, n-1); ex r_3; test5_true(emp, [b; n-1-1], r_3); Norm(emp, r_3)
  [Normed   Post] Norm(b=0, 0) \/ Norm(!b=0, 0) \/ ex r_3; test5_true(!b=0, [b; n-1-1], r_3); Norm(emp, r_3)
  
  [Entail  Check] true
  ==========================================
  
