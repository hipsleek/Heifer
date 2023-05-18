
  $ hip test_new_entail.ml 2>&1 | grep 'Function\|Entail.*Check' | ./check.py
  ALL OK!

  $ hip test_new_entail.ml 2>&1 | ./sanitize.sh
  before tactics
  Norm(emp, ()); Norm(emp, 0)
  <:
  Norm(emp, 0)
  
  norm, subsumption
  req emp; Norm(emp, 0)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => T ==> true
  (Norm post) T => 0=0 ==> true
  
  ========== Function: test10_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  <:
  Norm(emp, 0)
  
  norm, subsumption
  req emp; Norm(emp, 0)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => T ==> true
  (Norm post) T => 0=0 ==> true
  
  ========== Function: test6_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  <:
  Norm(emp, j)
  
  norm, subsumption
  req emp; Norm(emp, 0)
  <:
  req emp; Norm(emp, j)
  
  (Norm pre) T => T ==> true
  (Norm post) T => 0=j ==> false
  
  ========== Function: test7_false ==========
  [Specification] Norm(emp, j)
  [Normed   Spec] Norm(emp, j)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  <:
  Norm(emp, k)
  
  norm, subsumption
  req emp; Norm(emp, 0)
  <:
  req emp; Norm(emp, k)
  
  (Norm pre) T => T ==> true
  (Norm post) T => 0=k ==> false
  
  ========== Function: test8_false ==========
  [Specification] Norm(emp, k)
  [Normed   Spec] Norm(emp, k)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  <:
  ex r; Norm(emp, r)
  
  norm, subsumption
  req emp; Norm(emp, 0)
  <:
  ex r; req emp; Norm(emp, r)
  
  (Norm pre) T => T ==> true
  (Norm post) T => ex r. 0=r ==> true
  
  ========== Function: test9_true ==========
  [Specification] ex r; Norm(emp, r)
  [Normed   Spec] ex r; Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, f0)
  <:
  ex i; Norm(i->0, i)
  
  norm, subsumption
  ex f0; req emp; Norm(f0->0, f0)
  <:
  ex i; req emp; Norm(i->0, i)
  
  (Norm pre) T => ex f0. T ==> true
  (Norm post) T => ex i. f0=i/\0=0 ==> true
  
  ========== Function: test4_true ==========
  [Specification] ex i; Norm(i->0, i)
  [Normed   Spec] ex i; Norm(i->0, i)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, f0)
  [Normed   Post] ex f0; Norm(f0->0, f0)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+1)
  <:
  ex i; Norm(i->0, 1)
  
  norm, subsumption
  ex f0 i_1; req emp; Norm(f0->i_1 /\ i_1=0, i_1+1)
  <:
  ex i; req emp; Norm(i->0, 1)
  
  (Norm pre) T => ex f0,i_1. T ==> true
  (Norm post) i_1=0 => ex i. i_1+1=1/\0=i_1 ==> true
  
  ========== Function: test5_true ==========
  [Specification] ex i; Norm(i->0, 1)
  [Normed   Spec] ex i; Norm(i->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+1)
  [Normed   Post] ex f0 i_1; Norm(f0->i_1 /\ i_1=0, i_1+1)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+1); ex f2; req f0->f2; Norm(f0->i_1+1, ()); ex i_3; req f0->i_3; Norm(f0->i_3, i_3)
  <:
  ex i; Norm(i->1, 1)
  
  norm, subsumption
  ex f0 i_1 f2 i_3; req i_1=f2/\i_1+1=i_3; Norm(f0->i_3 /\ i_1=0/\f2=i_1/\i_3=i_1+1, i_3)
  <:
  ex i; req emp; Norm(i->1, 1)
  
  (Norm pre) T => ex f0,i_1,f2,i_3. i_1=f2/\i_1+1=i_3 ==> true
  (Norm post) i_1=0/\f2=i_1/\i_3=i_1+1/\i_1=f2/\i_1+1=i_3 => ex i. i_3=1/\1=i_3 ==> true
  
  ========== Function: test6_true ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+1); ex f2; req f0->f2; Norm(f0->i_1+1, ()); ex i_3; req f0->i_3; Norm(f0->i_3, i_3)
  [Normed   Post] ex f0 i_1 f2 i_3; req i_1=f2/\i_1+1=i_3; Norm(f0->i_3 /\ i_1=0/\f2=i_1/\i_3=i_1+1, i_3)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+2); ex f2; req f0->f2; Norm(f0->i_1+2, ()); ex i_3; req f0->i_3; Norm(f0->i_3, i_3)
  <:
  ex i; Norm(i->1, 1)
  
  norm, subsumption
  ex f0 i_1 f2 i_3; req i_1=f2/\i_1+2=i_3; Norm(f0->i_3 /\ i_1=0/\f2=i_1/\i_3=i_1+2, i_3)
  <:
  ex i; req emp; Norm(i->1, 1)
  
  (Norm pre) T => ex f0,i_1,f2,i_3. i_1=f2/\i_1+2=i_3 ==> true
  (Norm post) i_1=0/\f2=i_1/\i_3=i_1+2/\i_1=f2/\i_1+2=i_3 => ex i. i_3=1/\1=i_3 ==> false
  
  ========== Function: test23_false ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex i_1; req f0->i_1; Norm(f0->i_1, i_1); Norm(emp, i_1+2); ex f2; req f0->f2; Norm(f0->i_1+2, ()); ex i_3; req f0->i_3; Norm(f0->i_3, i_3)
  [Normed   Post] ex f0 i_1 f2 i_3; req i_1=f2/\i_1+2=i_3; Norm(f0->i_3 /\ i_1=0/\f2=i_1/\i_3=i_1+2, i_3)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, 1)
  <:
  ex r; Eff(emp, [], r)
  
  norm, subsumption
  ex res_0; req emp; Eff(emp, [], res_0); req emp; Norm(emp, 1)
  <:
  ex r; req emp; Eff(emp, [], r); ex n_8; req emp; Norm(emp, n_8)
  
  (Eff 0 pre) T => ex res_0. T ==> true
  (Eff 0 post) T => ex r. res_0=r ==> true
  (Norm pre) res_0=r => T ==> true
  (Norm post) res_0=r => ex n_8. 1=n_8 ==> true
  
  ========== Function: test19_true ==========
  [Specification] ex r; Eff(emp, [], r)
  [Normed   Spec] ex r; Eff(emp, [], r); ex n_2; Norm(emp, n_2)
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, 1)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, res_0)
  <:
  Eff(emp, [], ())
  
  norm, subsumption
  ex res_0; req emp; Eff(emp, [], res_0); req emp; Norm(emp, res_0)
  <:
  req emp; Eff(emp, [], ()); ex n_8; req emp; Norm(emp, n_8)
  
  (Eff 0 pre) T => ex res_0. T ==> true
  (Eff 0 post) T => res_0=() ==> false
  
  ========== Function: test25_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); ex n_2; Norm(emp, n_2)
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, res_0)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, res_0)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, 1)
  <:
  Eff(emp, [], ())
  
  norm, subsumption
  ex res_0; req emp; Eff(emp, [], res_0); req emp; Norm(emp, 1)
  <:
  req emp; Eff(emp, [], ()); ex n_8; req emp; Norm(emp, n_8)
  
  (Eff 0 pre) T => ex res_0. T ==> true
  (Eff 0 post) T => res_0=() ==> false
  
  ========== Function: test12_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); ex n_2; Norm(emp, n_2)
  
  [Raw Post Spec] Norm(emp, ()); ex res_0; Eff(emp, [], res_0); Norm(emp, res_0); Norm(emp, 1)
  [Normed   Post] ex res_0; Eff(emp, [], res_0); Norm(emp, 1)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); Norm(emp, res_1)
  <:
  ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f0 res_1; req emp; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+1 /\ f3=i_2, res_1)
  <:
  ex i ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f0,res_1. T ==> true
  (Eff 0 post) T => ex i,ret. res_1=ret/\0=0 ==> true
  (Norm pre) res_1=ret/\0=0 => ex i_2,f3. i_2=z/\i_2=f3 ==> true
  (Norm post) f3=i_2/\res_1=ret/\0=0/\i_2=z/\i_2=f3 => res_1=ret/\z+1=i_2+1 ==> true
  
  ========== Function: test21_true ==========
  [Specification] ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+1 /\ f3=i_2, res_1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); Norm(emp, res_1)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f0 res_1; req emp; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+1 /\ f3=i_2, res_1)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f0,res_1. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_1=ret/\0=0 ==> true
  (Norm pre) res_1=ret/\0=0 => ex i_2,f3. i_2=z/\i_2=f3 ==> true
  (Norm post) f3=i_2/\res_1=ret/\0=0/\i_2=z/\i_2=f3 => res_1=ret/\z+1=i_2+1 ==> true
  
  ========== Function: test0_true ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+1 /\ f3=i_2, res_1)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); ex i_4; req f0->i_4; Norm(f0->i_4, i_4)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f0 res_1; req emp; Eff(f0->0, [], res_1); ex i_2 f3 i_4; req f0->i_2 /\ i_2=f3/\i_2+1=i_4; Norm(f0->i_4 /\ f3=i_2/\i_4=i_2+1, i_4)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f0,res_1. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_1=ret/\0=0 ==> true
  (Norm pre) res_1=ret/\0=0 => ex i_2,f3,i_4. i_2=z/\i_2=f3/\i_2+1=i_4 ==> true
  (Norm post) f3=i_2/\i_4=i_2+1/\res_1=ret/\0=0/\i_2=z/\i_2=f3/\i_2+1=i_4 => i_4=ret/\z+1=i_4 ==> false
  
  ========== Function: test1_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+1); ex f3; req f0->f3; Norm(f0->i_2+1, ()); ex i_4; req f0->i_4; Norm(f0->i_4, i_4)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3 i_4; req f0->i_2 /\ i_2=f3/\i_2+1=i_4; Norm(f0->i_4 /\ f3=i_2/\i_4=i_2+1, i_4)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); Norm(emp, res_1)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f0 res_1; req emp; Eff(f0->0, [], res_1); req emp; Norm(emp, res_1)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f0,res_1. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_1=ret/\0=0 ==> true
  (Norm pre) i>0/\res_1=ret/\0=0 => T ==> true
  
  ========== Function: test2_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); Norm(emp, res_1)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+2); ex f3; req f0->f3; Norm(f0->i_2+2, ()); Norm(emp, res_1)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f0 res_1; req emp; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+2 /\ f3=i_2, res_1)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f0,res_1. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_1=ret/\0=0 ==> true
  (Norm pre) res_1=ret/\0=0 => ex i_2,f3. i_2=z/\i_2=f3 ==> true
  (Norm post) f3=i_2/\res_1=ret/\0=0/\i_2=z/\i_2=f3 => res_1=ret/\z+1=i_2+2 ==> false
  
  ========== Function: test3_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex res_1; Eff(emp, [], res_1); Norm(emp, res_1); ex i_2; req f0->i_2; Norm(f0->i_2, i_2); Norm(emp, i_2+2); ex f3; req f0->f3; Norm(f0->i_2+2, ()); Norm(emp, res_1)
  [Normed   Post] ex f0 res_1; Eff(f0->0, [], res_1); ex i_2 f3; req f0->i_2 /\ i_2=f3; Norm(f0->i_2+2 /\ f3=i_2, res_1)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->1, f1); Norm(emp, 1)
  <:
  ex a b; Norm(a->0*b->1, 1)
  
  norm, subsumption
  ex f0 f1; req emp; Norm(f0->0*f1->1, 1)
  <:
  ex a b; req emp; Norm(a->0*b->1, 1)
  
  (Norm pre) T => ex f0,f1. T ==> true
  (Norm post) T => ex a,b. 1=1/\1=1/\0=0 ==> true
  
  ========== Function: test13_true ==========
  [Specification] ex a b; Norm(a->0*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->0*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->1, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->1, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->2, f1); Norm(emp, 1)
  <:
  ex a b; Norm(a->1+1*b->0, 1)
  
  norm, subsumption
  ex f0 f1; req emp; Norm(f0->0*f1->2, 1)
  <:
  ex a b; req emp; Norm(a->1+1*b->0, 1)
  
  (Norm pre) T => ex f0,f1. T ==> true
  (Norm post) T => ex a,b. 1=1/\0=2/\1+1=0 ==> false
  (Norm post) T => ex a,b. 1=1/\0=0/\1+1=2 ==> true
  
  ========== Function: test18_true ==========
  [Specification] ex a b; Norm(a->1+1*b->0, 1)
  [Normed   Spec] ex a b; Norm(a->1+1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->2, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); req i->1; Norm(i->1, ()); ex f0; Norm(f0->2, f0); Norm(emp, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  norm, subsumption
  ex f0; req i->1; Norm(i->1*f0->2, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  (Norm pre) T => ex f0. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\2=2/\1=1 ==> true
  
  ========== Function: test20_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); req i->1; Norm(i->1, ()); ex f0; Norm(f0->2, f0); Norm(emp, 1)
  [Normed   Post] ex f0; req i->1; Norm(i->1*f0->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); req i->1; Norm(i->1, ()); ex f0; Norm(f0->2, f0); req f0->2; Norm(f0->2, ()); Norm(emp, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  norm, subsumption
  ex f0; req i->1; Norm(i->1*f0->2, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  (Norm pre) T => ex f0. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\2=2/\1=1 ==> true
  
  ========== Function: test21_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); req i->1; Norm(i->1, ()); ex f0; Norm(f0->2, f0); req f0->2; Norm(f0->2, ()); Norm(emp, 1)
  [Normed   Post] ex f0; req i->1; Norm(i->1*f0->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->2, f0); ex j_1; req f0->j_1; Norm(f0->j_1, j_1); req f0->j_1; Norm(f0->j_1, ())
  <:
  ex i a; Norm(i->a, ())
  
  norm, subsumption
  ex f0 j_1; req emp; Norm(f0->j_1 /\ j_1=2, ())
  <:
  ex i a; req emp; Norm(i->a, ())
  
  (Norm pre) T => ex f0,j_1. T ==> true
  (Norm post) j_1=2 => ex i,a. ()=()/\a=j_1 ==> true
  
  ========== Function: test22_true ==========
  [Specification] ex i a; Norm(i->a, ())
  [Normed   Spec] ex i a; Norm(i->a, ())
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->2, f0); ex j_1; req f0->j_1; Norm(f0->j_1, j_1); req f0->j_1; Norm(f0->j_1, ())
  [Normed   Post] ex f0 j_1; Norm(f0->j_1 /\ j_1=2, ())
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->1, f1); Norm(emp, 1)
  <:
  ex a b; Norm(a->1*b->1, 1)
  
  norm, subsumption
  ex f0 f1; req emp; Norm(f0->0*f1->1, 1)
  <:
  ex a b; req emp; Norm(a->1*b->1, 1)
  
  (Norm pre) T => ex f0,f1. T ==> true
  (Norm post) T => ex a,b. 1=1/\1=1/\1=0 ==> false
  (Norm post) T => ex a,b. 1=1/\1=0/\1=1 ==> false
  
  ========== Function: test14_false ==========
  [Specification] ex a b; Norm(a->1*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->1*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); ex f1; Norm(f1->1, f1); Norm(emp, 1)
  [Normed   Post] ex f0 f1; Norm(f0->0*f1->1, 1)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); req a->1; Norm(a->1, ()); Norm(emp, 1)
  <:
  req a->1; Norm(a->1, 1)
  
  norm, subsumption
  req a->1; Norm(a->1, 1)
  <:
  req a->1; Norm(a->1, 1)
  
  (Norm pre) T => 1=1 ==> true
  (Norm post) 1=1 => 1=1/\1=1 ==> true
  
  ========== Function: test15_true ==========
  [Specification] req a->1; Norm(a->1, 1)
  [Normed   Spec] req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); req a->1; Norm(a->1, ()); Norm(emp, 1)
  [Normed   Post] req a->1; Norm(a->1, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, 1)
  <:
  ex a; req a->1; Norm(a->1, 1)
  
  norm, subsumption
  ex f0; req emp; Norm(f0->0, 1)
  <:
  ex a; req a->1; Norm(a->1, 1)
  
  (Norm pre) a>0 => ex f0. T ==> true
  (Norm post) T => 1=1/\1=0 ==> false
  
  ========== Function: test16_false ==========
  [Specification] ex a; req a->1; Norm(a->1, 1)
  [Normed   Spec] ex a; req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; Norm(f0->0, f0); Norm(emp, 1)
  [Normed   Post] ex f0; Norm(f0->0, 1)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); req a->1; Norm(a->1, ()); ex f0; Norm(f0->0, f0); Norm(emp, 1)
  <:
  ex b; req a->1; Norm(a->1*b->0, 1)
  
  norm, subsumption
  ex f0; req a->1; Norm(a->1*f0->0, 1)
  <:
  ex b; req a->1; Norm(a->1*b->0, 1)
  
  (Norm pre) T => ex f0. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\0=0/\1=1 ==> true
  
  ========== Function: test17_true ==========
  [Specification] ex b; req a->1; Norm(a->1*b->0, 1)
  [Normed   Spec] ex b; req a->1; Norm(a->1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); req a->1; Norm(a->1, ()); ex f0; Norm(f0->0, f0); Norm(emp, 1)
  [Normed   Post] ex f0; req a->1; Norm(a->1*f0->0, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); Norm(emp, 1)
  <:
  Norm(emp, 1)
  
  norm, subsumption
  req emp; Norm(emp, 1)
  <:
  req emp; Norm(emp, 1)
  
  (Norm pre) T => T ==> true
  (Norm post) T => 1=1 ==> true
  
  ========== Function: f1 ==========
  [Specification] Norm(emp, 1)
  [Normed   Spec] Norm(emp, 1)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 1)
  [Normed   Post] Norm(emp, 1)
  
  [Entail  Check] true
  ==================================
  
  before tactics
  Norm(emp, ()); Norm(emp, 1); Norm(emp, 1)
  <:
  Norm(emp, 1)
  
  norm, subsumption
  req emp; Norm(emp, 1)
  <:
  req emp; Norm(emp, 1)
  
  (Norm pre) T => T ==> true
  (Norm post) T => 1=1 ==> true
  
  ========== Function: test24_true ==========
  [Specification] Norm(emp, 1)
  [Normed   Spec] Norm(emp, 1)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 1); Norm(emp, 1)
  [Normed   Post] Norm(emp, 1)
  
  [Entail  Check] true
  ===========================================
  

  $ hip test_ho.ml 2>&1 | grep 'Function\|Entail.*Check' | ./check.py
  TESTS FAILED
  ========== Function: test1_true ==========
  ========== Function: test2_true ==========
  ========== Function: test3_true ==========
  ========== Function: test6_true ==========

  $ hip test_ho.ml 2>&1 | ./sanitize.sh
  before tactics
  Norm(emp, ()); ex f0; f$(emp, [1], f0)
  <:
  ex r; f$(emp, [1], r); Norm(emp, r)
  
  norm, subsumption
  ex f0; req emp; f(emp, [1], f0); ex n_6; req emp; Norm(emp, n_6)
  <:
  ex r; req emp; f(emp, [1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => ex f0. T ==> true
  (Eff 0 post) T => ex r. f0=r/\1=1 ==> true
  (Norm pre) f0=r/\1=1 => ex n_6. T ==> true
  (Norm post) f0=r/\1=1 => n_6=r ==> false
  
  ========== Function: test1_true ==========
  [Specification] ex r; f$(emp, [1], r); Norm(emp, r)
  [Normed   Spec] ex r; f$(emp, [1], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; f$(emp, [1], f0)
  [Normed   Post] ex f0; f$(emp, [1], f0); ex n_4; Norm(emp, n_4)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f0; f$(emp, [1], f0); ex f1; g$(emp, [1], f1)
  <:
  ex r; ex s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  
  norm, subsumption
  ex f0; req emp; f(emp, [1], f0); ex f1; req emp; g(emp, [1], f1); ex n_10; req emp; Norm(emp, n_10)
  <:
  ex r s; req emp; f(emp, [1], r); req emp; g(emp, [2], s); req emp; Norm(emp, s)
  
  (Eff 0 pre) T => ex f0. T ==> true
  (Eff 0 post) T => ex r,s. f0=r/\1=1 ==> true
  (Eff 1 pre) f0=r/\1=1 => ex f1. T ==> true
  (Eff 1 post) f0=r/\1=1 => f1=s/\1=2 ==> false
  
  ========== Function: test2_true ==========
  [Specification] ex r; ex s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  [Normed   Spec] ex r s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; f$(emp, [1], f0); ex f1; g$(emp, [1], f1)
  [Normed   Post] ex f0; f$(emp, [1], f0); ex f1; g$(emp, [1], f1); ex n_7; Norm(emp, n_7)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f0; f$(emp, [1], f0); ex f1; g$(emp, [f0], f1)
  <:
  ex r; ex s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  
  norm, subsumption
  ex f0; req emp; f(emp, [1], f0); ex f1; req emp; g(emp, [f0], f1); ex n_10; req emp; Norm(emp, n_10)
  <:
  ex r s; req emp; f(emp, [1], r); req emp; g(emp, [r], s); req emp; Norm(emp, s)
  
  (Eff 0 pre) T => ex f0. T ==> true
  (Eff 0 post) T => ex r,s. f0=r/\1=1 ==> true
  (Eff 1 pre) f0=r/\1=1 => ex f1. T ==> true
  (Eff 1 post) f0=r/\1=1 => f1=s/\f0=r ==> false
  
  ========== Function: test3_true ==========
  [Specification] ex r; ex s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  [Normed   Spec] ex r s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  
  [Raw Post Spec] Norm(emp, ()); ex f0; f$(emp, [1], f0); ex f1; g$(emp, [f0], f1)
  [Normed   Post] ex f0; f$(emp, [1], f0); ex f1; g$(emp, [f0], f1); ex n_7; Norm(emp, n_7)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); test4_true$(emp, [()], r_2); Norm(emp, r_2)
  <:
  ex r; test4_true$(emp, [()], r); Norm(emp, r)
  
  norm, subsumption
  req emp; test4_true(emp, [()], r_2); req emp; Norm(emp, r_2)
  <:
  ex r; req emp; test4_true(emp, [()], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => T ==> true
  (Eff 0 post) T => ex r. r_2=r/\()=() ==> true
  (Norm pre) r_2=r/\()=() => T ==> true
  (Norm post) r_2=r/\()=() => r_2=r ==> true
  
  ========== Function: test4_true ==========
  [Specification] ex r; test4_true$(emp, [()], r); Norm(emp, r)
  [Normed   Spec] ex r; test4_true$(emp, [()], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); test4_true$(emp, [()], r_2); Norm(emp, r_2)
  [Normed   Post] test4_true$(emp, [()], r_2); Norm(emp, r_2)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test5_true$(emp, [b; n-1], r_2); Norm(emp, r_2)
  <:
  ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  
  unfold right
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test5_true$(emp, [b; n-1], r_2); Norm(emp, r_2)
  <:
  ex r; Norm(r=0, r); Norm(emp, r) \/ ex r; test5_true$(emp, [b; n-1], r); Norm(emp, r); Norm(emp, r)
  
  norm, subsumption
  req emp; Norm(b=0, 0)
  <:
  ex r; req emp; Norm(r=0, r)
  
  (Norm pre) T => T ==> true
  (Norm post) b=0 => ex r. 0=r/\r=0 ==> true
  norm, subsumption
  req emp; test5_true(!b=1, [b; n-1], r_2); req emp; Norm(emp, r_2)
  <:
  ex r; req emp; Norm(r=0, r)
  
  FAIL, unequal length
  req emp; test5_true(!b=1, [b; n-1], r_2); req emp; Norm(emp, r_2)
  |=
  ex r; req emp; Norm(r=0, r)
  
  norm, subsumption
  req emp; test5_true(!b=1, [b; n-1], r_2); req emp; Norm(emp, r_2)
  <:
  ex r; req emp; test5_true(emp, [b; n-1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => T ==> true
  (Eff 0 post) !b=1 => ex r. r_2=r/\n-1=n-1/\b=b ==> true
  (Norm pre) r_2=r/\n-1=n-1/\b=b => T ==> true
  (Norm post) r_2=r/\n-1=n-1/\b=b => r_2=r ==> true
  
  ========== Function: test5_true ==========
  [Specification] ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  [Normed   Spec] ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test5_true$(emp, [b; n-1], r_2); Norm(emp, r_2)
  [Normed   Post] Norm(b=0, 0) \/ test5_true$(!b=1, [b; n-1], r_2); Norm(emp, r_2)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test6_true$(emp, [b; n-1-1], r_3); Norm(emp, r_3)
  <:
  Norm(emp, 0) \/ ex r; test6_true$(emp, [b; n-1], r); Norm(emp, r)
  
  norm, subsumption
  req emp; Norm(b=0, 0)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => T ==> true
  (Norm post) b=0 => 0=0 ==> true
  norm, subsumption
  req emp; Norm(!b=1, 0)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => T ==> true
  (Norm post) !b=1 => 0=0 ==> true
  norm, subsumption
  req emp; test6_true(!b=1, [b; n-1-1], r_3); req emp; Norm(emp, r_3)
  <:
  req emp; Norm(emp, 0)
  
  FAIL, unequal length
  req emp; test6_true(!b=1, [b; n-1-1], r_3); req emp; Norm(emp, r_3)
  |=
  req emp; Norm(emp, 0)
  
  norm, subsumption
  req emp; test6_true(!b=1, [b; n-1-1], r_3); req emp; Norm(emp, r_3)
  <:
  ex r; req emp; test6_true(emp, [b; n-1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => T ==> true
  (Eff 0 post) !b=1 => ex r. r_3=r/\n-1-1=n-1/\b=b ==> false
  
  ========== Function: test6_true ==========
  [Specification] Norm(emp, 0) \/ ex r; test6_true$(emp, [b; n-1], r); Norm(emp, r)
  [Normed   Spec] Norm(emp, 0) \/ ex r; test6_true$(emp, [b; n-1], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test6_true$(emp, [b; n-1-1], r_3); Norm(emp, r_3)
  [Normed   Post] Norm(b=0, 0) \/ Norm(!b=1, 0) \/ test6_true$(!b=1, [b; n-1-1], r_3); Norm(emp, r_3)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test7_false$(emp, [b; n-1], r_2); Norm(emp, r_2)
  <:
  ex r; test7_false$(emp, [b; n], r); Norm(emp, r)
  
  norm, subsumption
  req emp; Norm(b=0, 0)
  <:
  ex r; req emp; test7_false(emp, [b; n], r); req emp; Norm(emp, r)
  
  FAIL, unequal length
  req emp; Norm(b=0, 0)
  |=
  ex r; req emp; test7_false(emp, [b; n], r); req emp; Norm(emp, r)
  
  
  ========== Function: test7_false ==========
  [Specification] ex r; test7_false$(emp, [b; n], r); Norm(emp, r)
  [Normed   Spec] ex r; test7_false$(emp, [b; n], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test7_false$(emp, [b; n-1], r_2); Norm(emp, r_2)
  [Normed   Post] Norm(b=0, 0) \/ test7_false$(!b=1, [b; n-1], r_2); Norm(emp, r_2)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  <:
  Norm(emp, 0)
  
  unfold left
  Norm(emp, ()); Norm(r_2=0, r_2); Norm(emp, r_2) \/ Norm(emp, ()); test5_true$(emp, [b; n-1], r_2); Norm(emp, r_2); Norm(emp, r_2)
  <:
  Norm(emp, 0)
  
  apply ih
  Norm(emp, ()); Norm(r_2=0, r_2); Norm(emp, r_2)
  <:
  Norm(emp, 0)
  
  norm, subsumption
  req emp; Norm(r_2=0, r_2)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => T ==> true
  (Norm post) r_2=0 => r_2=0 ==> true
  
  ========== Function: test8_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  [Normed   Post] test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  <:
  Norm(emp, 1)
  
  unfold left
  Norm(emp, ()); Norm(r_2=0, r_2); Norm(emp, r_2) \/ Norm(emp, ()); test5_true$(emp, [b; n-1], r_2); Norm(emp, r_2); Norm(emp, r_2)
  <:
  Norm(emp, 1)
  
  apply ih
  Norm(emp, ()); Norm(r_2=0, r_2); Norm(emp, r_2)
  <:
  Norm(emp, 1)
  
  norm, subsumption
  req emp; Norm(r_2=0, r_2)
  <:
  req emp; Norm(emp, 1)
  
  (Norm pre) T => T ==> true
  (Norm post) r_2=0 => r_2=1 ==> false
  
  ========== Function: test9_false ==========
  [Specification] Norm(emp, 1)
  [Normed   Spec] Norm(emp, 1)
  
  [Raw Post Spec] Norm(emp, ()); test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  [Normed   Post] test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  <:
  Norm(emp, 0)
  
  unfold left
  Norm(emp, ()); Norm(r_2=0, r_2); Norm(emp, r_2) \/ Norm(emp, ()); test5_true$(emp, [b; n-1], r_2); Norm(emp, r_2); Norm(emp, r_2)
  <:
  Norm(emp, 0)
  
  norm, subsumption
  req emp; Norm(r_2=0, r_2)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => T ==> true
  (Norm post) r_2=0 => r_2=0 ==> true
  norm, subsumption
  req emp; test5_true(emp, [b; n-1], r_2); req emp; Norm(emp, r_2)
  <:
  req emp; Norm(emp, 0)
  
  FAIL, unequal length
  req emp; test5_true(emp, [b; n-1], r_2); req emp; Norm(emp, r_2)
  |=
  req emp; Norm(emp, 0)
  
  
  ========== Function: test10_false ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  [Normed   Post] test5_true$(emp, [b; n], r_2); Norm(emp, r_2)
  
  [Entail  Check] false
  ============================================
  
