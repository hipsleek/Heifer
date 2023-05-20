
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
  Norm(emp, ()); ex f48; Norm(f48->0, f48); Norm(emp, f48)
  <:
  ex i; Norm(i->0, i)
  
  norm, subsumption
  ex f48; req emp; Norm(f48->0, f48)
  <:
  ex i; req emp; Norm(i->0, i)
  
  (Norm pre) T => ex f48. T ==> true
  (Norm post) T => ex i. f48=i/\0=0 ==> true
  
  ========== Function: test4_true ==========
  [Specification] ex i; Norm(i->0, i)
  [Normed   Spec] ex i; Norm(i->0, i)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); Norm(emp, f48)
  [Normed   Post] ex f48; Norm(f48->0, f48)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex i_49; req f48->i_49; Norm(f48->i_49, i_49); Norm(emp, i_49+1)
  <:
  ex i; Norm(i->0, 1)
  
  norm, subsumption
  ex f48 i_49; req emp; Norm(f48->i_49 /\ i_49=0, i_49+1)
  <:
  ex i; req emp; Norm(i->0, 1)
  
  (Norm pre) T => ex f48,i_49. T ==> true
  (Norm post) i_49=0 => ex i. i_49+1=1/\0=i_49 ==> true
  
  ========== Function: test5_true ==========
  [Specification] ex i; Norm(i->0, 1)
  [Normed   Spec] ex i; Norm(i->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex i_49; req f48->i_49; Norm(f48->i_49, i_49); Norm(emp, i_49+1)
  [Normed   Post] ex f48 i_49; Norm(f48->i_49 /\ i_49=0, i_49+1)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex i_49; req f48->i_49; Norm(f48->i_49, i_49); Norm(emp, i_49+1); ex f50; req f48->f50; Norm(f48->i_49+1, ()); ex i_51; req f48->i_51; Norm(f48->i_51, i_51)
  <:
  ex i; Norm(i->1, 1)
  
  norm, subsumption
  ex f48 i_49 f50 i_51; req i_49=f50/\i_49+1=i_51; Norm(f48->i_51 /\ i_49=0/\f50=i_49/\i_51=i_49+1, i_51)
  <:
  ex i; req emp; Norm(i->1, 1)
  
  (Norm pre) T => ex f48,i_49,f50,i_51. i_49=f50/\i_49+1=i_51 ==> true
  (Norm post) i_49=0/\f50=i_49/\i_51=i_49+1/\i_49=f50/\i_49+1=i_51 => ex i. i_51=1/\1=i_51 ==> true
  
  ========== Function: test6_true ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex i_49; req f48->i_49; Norm(f48->i_49, i_49); Norm(emp, i_49+1); ex f50; req f48->f50; Norm(f48->i_49+1, ()); ex i_51; req f48->i_51; Norm(f48->i_51, i_51)
  [Normed   Post] ex f48 i_49 f50 i_51; req i_49=f50/\i_49+1=i_51; Norm(f48->i_51 /\ i_49=0/\f50=i_49/\i_51=i_49+1, i_51)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex i_49; req f48->i_49; Norm(f48->i_49, i_49); Norm(emp, i_49+2); ex f50; req f48->f50; Norm(f48->i_49+2, ()); ex i_51; req f48->i_51; Norm(f48->i_51, i_51)
  <:
  ex i; Norm(i->1, 1)
  
  norm, subsumption
  ex f48 i_49 f50 i_51; req i_49=f50/\i_49+2=i_51; Norm(f48->i_51 /\ i_49=0/\f50=i_49/\i_51=i_49+2, i_51)
  <:
  ex i; req emp; Norm(i->1, 1)
  
  (Norm pre) T => ex f48,i_49,f50,i_51. i_49=f50/\i_49+2=i_51 ==> true
  (Norm post) i_49=0/\f50=i_49/\i_51=i_49+2/\i_49=f50/\i_49+2=i_51 => ex i. i_51=1/\1=i_51 ==> false
  
  ========== Function: test23_false ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex i_49; req f48->i_49; Norm(f48->i_49, i_49); Norm(emp, i_49+2); ex f50; req f48->f50; Norm(f48->i_49+2, ()); ex i_51; req f48->i_51; Norm(f48->i_51, i_51)
  [Normed   Post] ex f48 i_49 f50 i_51; req i_49=f50/\i_49+2=i_51; Norm(f48->i_51 /\ i_49=0/\f50=i_49/\i_51=i_49+2, i_51)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, res_48)
  <:
  ex r; Eff(emp, [], r)
  
  norm, subsumption
  ex res_48; req emp; Eff(emp, [], res_48); req emp; Norm(emp, res_48)
  <:
  ex r; req emp; Eff(emp, [], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => ex res_48. T ==> true
  (Eff 0 post) T => ex r. res_48=r ==> true
  (Norm pre) res_48=r => T ==> true
  (Norm post) res_48=r => res_48=r ==> true
  
  ========== Function: test19_true ==========
  [Specification] ex r; Eff(emp, [], r)
  [Normed   Spec] ex r; Eff(emp, [], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, res_48)
  [Normed   Post] ex res_48; Eff(emp, [], res_48); Norm(emp, res_48)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, 1)
  <:
  ex r; Eff(emp, [], r); ex r1; Norm(emp, r1)
  
  norm, subsumption
  ex res_48; req emp; Eff(emp, [], res_48); req emp; Norm(emp, 1)
  <:
  ex r; req emp; Eff(emp, [], r); ex r1; req emp; Norm(emp, r1)
  
  (Eff 0 pre) T => ex res_48. T ==> true
  (Eff 0 post) T => ex r. res_48=r ==> true
  (Norm pre) res_48=r => T ==> true
  (Norm post) res_48=r => ex r1. 1=r1 ==> true
  
  ========== Function: test27_true ==========
  [Specification] ex r; Eff(emp, [], r); ex r1; Norm(emp, r1)
  [Normed   Spec] ex r; Eff(emp, [], r); ex r1; Norm(emp, r1)
  
  [Raw Post Spec] Norm(emp, ()); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, 1)
  [Normed   Post] ex res_48; Eff(emp, [], res_48); Norm(emp, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, res_48)
  <:
  Eff(emp, [], ())
  
  norm, subsumption
  ex res_48; req emp; Eff(emp, [], res_48); req emp; Norm(emp, res_48)
  <:
  req emp; Eff(emp, [], ()); req emp; Norm(emp, ())
  
  (Eff 0 pre) T => ex res_48. T ==> true
  (Eff 0 post) T => res_48=() ==> false
  
  ========== Function: test25_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); Norm(emp, ())
  
  [Raw Post Spec] Norm(emp, ()); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, res_48)
  [Normed   Post] ex res_48; Eff(emp, [], res_48); Norm(emp, res_48)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, 1)
  <:
  Eff(emp, [], ())
  
  norm, subsumption
  ex res_48; req emp; Eff(emp, [], res_48); req emp; Norm(emp, 1)
  <:
  req emp; Eff(emp, [], ()); req emp; Norm(emp, ())
  
  (Eff 0 pre) T => ex res_48. T ==> true
  (Eff 0 post) T => res_48=() ==> false
  
  ========== Function: test12_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); Norm(emp, ())
  
  [Raw Post Spec] Norm(emp, ()); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, 1)
  [Normed   Post] ex res_48; Eff(emp, [], res_48); Norm(emp, 1)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); ex i_50; req f48->i_50; Norm(f48->i_50, i_50); Norm(emp, i_50+1); ex f51; req f48->f51; Norm(f48->i_50+1, ()); Norm(emp, res_49)
  <:
  ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f48 res_49; req emp; Eff(f48->0, [], res_49); ex i_50 f51; req f48->i_50 /\ i_50=f51; Norm(f48->i_50+1 /\ f51=i_50, res_49)
  <:
  ex i ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f48,res_49. T ==> true
  (Eff 0 post) T => ex i,ret. res_49=ret/\0=0 ==> true
  (Norm pre) res_49=ret/\0=0 => ex i_50,f51. i_50=z/\i_50=f51 ==> true
  (Norm post) f51=i_50/\i_50=z/\i_50=f51/\res_49=ret/\0=0 => res_49=ret/\z+1=i_50+1 ==> true
  
  ========== Function: test21_true ==========
  [Specification] ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); ex i_50; req f48->i_50; Norm(f48->i_50, i_50); Norm(emp, i_50+1); ex f51; req f48->f51; Norm(f48->i_50+1, ()); Norm(emp, res_49)
  [Normed   Post] ex f48 res_49; Eff(f48->0, [], res_49); ex i_50 f51; req f48->i_50 /\ i_50=f51; Norm(f48->i_50+1 /\ f51=i_50, res_49)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); ex i_50; req f48->i_50; Norm(f48->i_50, i_50); Norm(emp, i_50+1); ex f51; req f48->f51; Norm(f48->i_50+1, ()); Norm(emp, res_49)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f48 res_49; req emp; Eff(f48->0, [], res_49); ex i_50 f51; req f48->i_50 /\ i_50=f51; Norm(f48->i_50+1 /\ f51=i_50, res_49)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f48,res_49. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_49=ret/\0=0 ==> true
  (Norm pre) res_49=ret/\0=0 => ex i_50,f51. i_50=z/\i_50=f51 ==> true
  (Norm post) f51=i_50/\i_50=z/\i_50=f51/\res_49=ret/\0=0 => res_49=ret/\z+1=i_50+1 ==> true
  
  ========== Function: test0_true ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); ex i_50; req f48->i_50; Norm(f48->i_50, i_50); Norm(emp, i_50+1); ex f51; req f48->f51; Norm(f48->i_50+1, ()); Norm(emp, res_49)
  [Normed   Post] ex f48 res_49; Eff(f48->0, [], res_49); ex i_50 f51; req f48->i_50 /\ i_50=f51; Norm(f48->i_50+1 /\ f51=i_50, res_49)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); ex i_50; req f48->i_50; Norm(f48->i_50, i_50); Norm(emp, i_50+1); ex f51; req f48->f51; Norm(f48->i_50+1, ()); ex i_52; req f48->i_52; Norm(f48->i_52, i_52)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f48 res_49; req emp; Eff(f48->0, [], res_49); ex i_50 f51 i_52; req f48->i_50 /\ i_50=f51/\i_50+1=i_52; Norm(f48->i_52 /\ f51=i_50/\i_52=i_50+1, i_52)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f48,res_49. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_49=ret/\0=0 ==> true
  (Norm pre) res_49=ret/\0=0 => ex i_50,f51,i_52. i_50=z/\i_50=f51/\i_50+1=i_52 ==> true
  (Norm post) f51=i_50/\i_52=i_50+1/\i_50=z/\i_50=f51/\i_50+1=i_52/\res_49=ret/\0=0 => i_52=ret/\z+1=i_52 ==> false
  
  ========== Function: test1_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); ex i_50; req f48->i_50; Norm(f48->i_50, i_50); Norm(emp, i_50+1); ex f51; req f48->f51; Norm(f48->i_50+1, ()); ex i_52; req f48->i_52; Norm(f48->i_52, i_52)
  [Normed   Post] ex f48 res_49; Eff(f48->0, [], res_49); ex i_50 f51 i_52; req f48->i_50 /\ i_50=f51/\i_50+1=i_52; Norm(f48->i_52 /\ f51=i_50/\i_52=i_50+1, i_52)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); Norm(emp, res_49)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f48 res_49; req emp; Eff(f48->0, [], res_49); req emp; Norm(emp, res_49)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f48,res_49. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_49=ret/\0=0 ==> true
  (Norm pre) i>0/\res_49=ret/\0=0 => T ==> true
  
  ========== Function: test2_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); Norm(emp, res_49)
  [Normed   Post] ex f48 res_49; Eff(f48->0, [], res_49); Norm(emp, res_49)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); ex i_50; req f48->i_50; Norm(f48->i_50, i_50); Norm(emp, i_50+2); ex f51; req f48->f51; Norm(f48->i_50+2, ()); Norm(emp, res_49)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f48 res_49; req emp; Eff(f48->0, [], res_49); ex i_50 f51; req f48->i_50 /\ i_50=f51; Norm(f48->i_50+2 /\ f51=i_50, res_49)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f48,res_49. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_49=ret/\0=0 ==> true
  (Norm pre) res_49=ret/\0=0 => ex i_50,f51. i_50=z/\i_50=f51 ==> true
  (Norm post) f51=i_50/\i_50=z/\i_50=f51/\res_49=ret/\0=0 => res_49=ret/\z+1=i_50+2 ==> false
  
  ========== Function: test3_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex res_49; Eff(emp, [], res_49); Norm(emp, res_49); ex i_50; req f48->i_50; Norm(f48->i_50, i_50); Norm(emp, i_50+2); ex f51; req f48->f51; Norm(f48->i_50+2, ()); Norm(emp, res_49)
  [Normed   Post] ex f48 res_49; Eff(f48->0, [], res_49); ex i_50 f51; req f48->i_50 /\ i_50=f51; Norm(f48->i_50+2 /\ f51=i_50, res_49)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex f49; Norm(f49->1, f49); Norm(emp, 1)
  <:
  ex a b; Norm(a->0*b->1, 1)
  
  norm, subsumption
  ex f48 f49; req emp; Norm(f48->0*f49->1, 1)
  <:
  ex a b; req emp; Norm(a->0*b->1, 1)
  
  (Norm pre) T => ex f48,f49. T ==> true
  (Norm post) T => ex a,b. 1=1/\1=1/\0=0 ==> true
  
  ========== Function: test13_true ==========
  [Specification] ex a b; Norm(a->0*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->0*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex f49; Norm(f49->1, f49); Norm(emp, 1)
  [Normed   Post] ex f48 f49; Norm(f48->0*f49->1, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex f49; Norm(f49->2, f49); Norm(emp, 1)
  <:
  ex a b; Norm(a->1+1*b->0, 1)
  
  norm, subsumption
  ex f48 f49; req emp; Norm(f48->0*f49->2, 1)
  <:
  ex a b; req emp; Norm(a->1+1*b->0, 1)
  
  (Norm pre) T => ex f48,f49. T ==> true
  (Norm post) T => ex a,b. 1=1/\0=2/\1+1=0 ==> false
  (Norm post) T => ex a,b. 1=1/\0=0/\1+1=2 ==> true
  
  ========== Function: test18_true ==========
  [Specification] ex a b; Norm(a->1+1*b->0, 1)
  [Normed   Spec] ex a b; Norm(a->1+1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex f49; Norm(f49->2, f49); Norm(emp, 1)
  [Normed   Post] ex f48 f49; Norm(f48->0*f49->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); req i->1; Norm(i->1, ()); ex f48; Norm(f48->2, f48); Norm(emp, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  norm, subsumption
  ex f48; req i->1; Norm(i->1*f48->2, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  (Norm pre) T => ex f48. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\2=2/\1=1 ==> true
  
  ========== Function: test20_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); req i->1; Norm(i->1, ()); ex f48; Norm(f48->2, f48); Norm(emp, 1)
  [Normed   Post] ex f48; req i->1; Norm(i->1*f48->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); req i->1; Norm(i->1, ()); ex f48; Norm(f48->2, f48); req f48->2; Norm(f48->2, ()); Norm(emp, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  norm, subsumption
  ex f48; req i->1; Norm(i->1*f48->2, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  (Norm pre) T => ex f48. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\2=2/\1=1 ==> true
  
  ========== Function: test21_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); req i->1; Norm(i->1, ()); ex f48; Norm(f48->2, f48); req f48->2; Norm(f48->2, ()); Norm(emp, 1)
  [Normed   Post] ex f48; req i->1; Norm(i->1*f48->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->2, f48); ex j_49; req f48->j_49; Norm(f48->j_49, j_49); req f48->j_49; Norm(f48->j_49, ())
  <:
  ex i a; Norm(i->a, ())
  
  norm, subsumption
  ex f48 j_49; req emp; Norm(f48->j_49 /\ j_49=2, ())
  <:
  ex i a; req emp; Norm(i->a, ())
  
  (Norm pre) T => ex f48,j_49. T ==> true
  (Norm post) j_49=2 => ex i,a. ()=()/\a=j_49 ==> true
  
  ========== Function: test22_true ==========
  [Specification] ex i a; Norm(i->a, ())
  [Normed   Spec] ex i a; Norm(i->a, ())
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->2, f48); ex j_49; req f48->j_49; Norm(f48->j_49, j_49); req f48->j_49; Norm(f48->j_49, ())
  [Normed   Post] ex f48 j_49; Norm(f48->j_49 /\ j_49=2, ())
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex f49; Norm(f49->1, f49); Norm(emp, 1)
  <:
  ex a b; Norm(a->1*b->1, 1)
  
  norm, subsumption
  ex f48 f49; req emp; Norm(f48->0*f49->1, 1)
  <:
  ex a b; req emp; Norm(a->1*b->1, 1)
  
  (Norm pre) T => ex f48,f49. T ==> true
  (Norm post) T => ex a,b. 1=1/\1=1/\1=0 ==> false
  (Norm post) T => ex a,b. 1=1/\1=0/\1=1 ==> false
  
  ========== Function: test14_false ==========
  [Specification] ex a b; Norm(a->1*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->1*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex f49; Norm(f49->1, f49); Norm(emp, 1)
  [Normed   Post] ex f48 f49; Norm(f48->0*f49->1, 1)
  
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
  Norm(emp, ()); ex f48; Norm(f48->0, f48); Norm(emp, 1)
  <:
  ex a; req a->1; Norm(a->1, 1)
  
  norm, subsumption
  ex f48; req emp; Norm(f48->0, 1)
  <:
  ex a; req a->1; Norm(a->1, 1)
  
  (Norm pre) a>0 => ex f48. T ==> true
  (Norm post) a>0 => 1=1/\1=0 ==> false
  
  ========== Function: test16_false ==========
  [Specification] ex a; req a->1; Norm(a->1, 1)
  [Normed   Spec] ex a; req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); Norm(emp, 1)
  [Normed   Post] ex f48; Norm(f48->0, 1)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); req a->1; Norm(a->1, ()); ex f48; Norm(f48->0, f48); Norm(emp, 1)
  <:
  ex b; req a->1; Norm(a->1*b->0, 1)
  
  norm, subsumption
  ex f48; req a->1; Norm(a->1*f48->0, 1)
  <:
  ex b; req a->1; Norm(a->1*b->0, 1)
  
  (Norm pre) T => ex f48. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\0=0/\1=1 ==> true
  
  ========== Function: test17_true ==========
  [Specification] ex b; req a->1; Norm(a->1*b->0, 1)
  [Normed   Spec] ex b; req a->1; Norm(a->1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); req a->1; Norm(a->1, ()); ex f48; Norm(f48->0, f48); Norm(emp, 1)
  [Normed   Post] ex f48; req a->1; Norm(a->1*f48->0, 1)
  
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
  
  before tactics
  Norm(emp, ()); Norm(emp, a+1)
  <:
  req a=1; Norm(emp, 2)
  
  norm, subsumption
  req emp; Norm(emp, a+1)
  <:
  req a=1; Norm(emp, 2)
  
  (Norm pre) a=1 => T ==> true
  (Norm post) a=1 => a+1=2 ==> true
  
  ========== Function: fa ==========
  [Specification] req a=1; Norm(emp, 2)
  [Normed   Spec] req a=1; Norm(emp, 2)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, a+1)
  [Normed   Post] Norm(emp, a+1)
  
  [Entail  Check] true
  ==================================
  
  before tactics
  Norm(emp, ()); req 1=1; Norm(emp, 2); Norm(emp, 2)
  <:
  Norm(emp, 2)
  
  norm, subsumption
  req 1=1; Norm(emp, 2)
  <:
  req emp; Norm(emp, 2)
  
  (Norm pre) T => 1=1 ==> true
  (Norm post) 1=1 => 2=2 ==> true
  
  ========== Function: test26_true ==========
  [Specification] Norm(emp, 2)
  [Normed   Spec] Norm(emp, 2)
  
  [Raw Post Spec] Norm(emp, ()); req 1=1; Norm(emp, 2); Norm(emp, 2)
  [Normed   Post] req 1=1; Norm(emp, 2)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f48; Norm(f48->0, f48); ex f49; Norm(f49->0, f49); ex res_50; E(emp, [], res_50); Norm(emp, res_50); ex i_51; req f48->i_51; Norm(f48->i_51, i_51); Norm(emp, i_51+1); ex f52; req f48->f52; Norm(f48->i_51+1, ()); ex j_53; req f49->j_53; Norm(f49->j_53, j_53); Norm(emp, j_53+1); ex f54; req f49->f54; Norm(f49->j_53+1, ()); Norm(emp, res_50)
  <:
  ex i j z1 z2 ret; E(i->0*j->0, [], ret); req i->z1*j->z2; Norm(i->z1+1*j->z2+1, ret)
  
  norm, subsumption
  ex f48 f49 res_50; req emp; E(f48->0*f49->0, [], res_50); ex i_51 f52 j_53 f54; req f48->i_51*f49->j_53 /\ i_51=f52/\j_53=f54; Norm(f48->i_51+1*f49->j_53+1 /\ f52=i_51/\f54=j_53, res_50)
  <:
  ex i j z1 z2 ret; req emp; E(i->0*j->0, [], ret); req i->z1*j->z2*emp; Norm(i->z1+1*j->z2+1, ret)
  
  (Eff 0 pre) T => ex f48,f49,res_50. T ==> true
  (Eff 0 post) T => ex i,j,z1,z2,ret. res_50=ret/\0=0/\0=0 ==> true
  (Norm pre) res_50=ret/\0=0/\0=0 => ex i_51,f52,j_53,f54. j_53=z2/\i_51=z1/\i_51=f52/\j_53=f54 ==> true
  (Norm post) f52=i_51/\f54=j_53/\j_53=z2/\i_51=z1/\i_51=f52/\j_53=f54/\res_50=ret/\0=0/\0=0 => res_50=ret/\z2+1=j_53+1/\z1+1=i_51+1 ==> true
  
  ========== Function: two_locations_true ==========
  [Specification] ex i j z1 z2 ret; E(i->0*j->0, [], ret); req i->z1*j->z2; Norm(i->z1+1*j->z2+1, ret)
  [Normed   Spec] ex i j z1 z2 ret; E(i->0*j->0, [], ret); req i->z1*j->z2*emp; Norm(i->z1+1*j->z2+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f48; Norm(f48->0, f48); ex f49; Norm(f49->0, f49); ex res_50; E(emp, [], res_50); Norm(emp, res_50); ex i_51; req f48->i_51; Norm(f48->i_51, i_51); Norm(emp, i_51+1); ex f52; req f48->f52; Norm(f48->i_51+1, ()); ex j_53; req f49->j_53; Norm(f49->j_53, j_53); Norm(emp, j_53+1); ex f54; req f49->f54; Norm(f49->j_53+1, ()); Norm(emp, res_50)
  [Normed   Post] ex f48 f49 res_50; E(f48->0*f49->0, [], res_50); ex i_51 f52 j_53 f54; req f48->i_51*f49->j_53 /\ i_51=f52/\j_53=f54; Norm(f48->i_51+1*f49->j_53+1 /\ f52=i_51/\f54=j_53, res_50)
  
  [Entail  Check] true
  ==================================================
  

  $ hip test_ho.ml 2>&1 | grep 'Function\|Entail.*Check' | ./check.py
  TESTS FAILED
  ========== Function: test2_true ==========
  ========== Function: test3_true ==========
  ========== Function: test6_true ==========

  $ hip test_ho.ml 2>&1 | ./sanitize.sh
  before tactics
  Norm(emp, ()); ex f6; f$(emp, [1], f6)
  <:
  ex r; f$(emp, [1], r); Norm(emp, r)
  
  norm, subsumption
  ex f6; req emp; f(emp, [1], f6); req emp; Norm(emp, f6)
  <:
  ex r; req emp; f(emp, [1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => ex f6. T ==> true
  (Eff 0 post) T => ex r. f6=r/\1=1 ==> true
  (Norm pre) f6=r/\1=1 => T ==> true
  (Norm post) f6=r/\1=1 => f6=r ==> true
  
  ========== Function: test1_true ==========
  [Specification] ex r; f$(emp, [1], r); Norm(emp, r)
  [Normed   Spec] ex r; f$(emp, [1], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); ex f6; f$(emp, [1], f6)
  [Normed   Post] ex f6; f$(emp, [1], f6); Norm(emp, f6)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f6; f$(emp, [1], f6); ex f7; g$(emp, [1], f7)
  <:
  ex r; ex s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  
  norm, subsumption
  ex f6; req emp; f(emp, [1], f6); ex f7; req emp; g(emp, [1], f7); req emp; Norm(emp, f7)
  <:
  ex r s; req emp; f(emp, [1], r); req emp; g(emp, [2], s); req emp; Norm(emp, s)
  
  (Eff 0 pre) T => ex f6. T ==> true
  (Eff 0 post) T => ex r,s. f6=r/\1=1 ==> true
  (Eff 1 pre) f6=r/\1=1 => ex f7. T ==> true
  (Eff 1 post) f6=r/\1=1 => f7=s/\1=2 ==> false
  
  ========== Function: test2_true ==========
  [Specification] ex r; ex s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  [Normed   Spec] ex r s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  
  [Raw Post Spec] Norm(emp, ()); ex f6; f$(emp, [1], f6); ex f7; g$(emp, [1], f7)
  [Normed   Post] ex f6; f$(emp, [1], f6); ex f7; g$(emp, [1], f7); Norm(emp, f7)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f6; f$(emp, [1], f6); ex f7; g$(emp, [f6], f7)
  <:
  ex r; ex s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  
  norm, subsumption
  ex f6; req emp; f(emp, [1], f6); ex f7; req emp; g(emp, [f6], f7); req emp; Norm(emp, f7)
  <:
  ex r s; req emp; f(emp, [1], r); req emp; g(emp, [r], s); req emp; Norm(emp, s)
  
  (Eff 0 pre) T => ex f6. T ==> true
  (Eff 0 post) T => ex r,s. f6=r/\1=1 ==> true
  (Eff 1 pre) f6=r/\1=1 => ex f7. T ==> true
  (Eff 1 post) f6=r/\1=1 => f7=s/\f6=r ==> false
  
  ========== Function: test3_true ==========
  [Specification] ex r; ex s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  [Normed   Spec] ex r s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  
  [Raw Post Spec] Norm(emp, ()); ex f6; f$(emp, [1], f6); ex f7; g$(emp, [f6], f7)
  [Normed   Post] ex f6; f$(emp, [1], f6); ex f7; g$(emp, [f6], f7); Norm(emp, f7)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); ex r_7; test4_true$(emp, [()], r_7); Norm(emp, r_7)
  <:
  ex r; test4_true$(emp, [()], r); Norm(emp, r)
  
  norm, subsumption
  ex r_7; req emp; test4_true(emp, [()], r_7); req emp; Norm(emp, r_7)
  <:
  ex r; req emp; test4_true(emp, [()], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => ex r_7. T ==> true
  (Eff 0 post) T => ex r. r_7=r/\()=() ==> true
  (Norm pre) r_7=r/\()=() => T ==> true
  (Norm post) r_7=r/\()=() => r_7=r ==> true
  
  ========== Function: test4_true ==========
  [Specification] ex r; test4_true$(emp, [()], r); Norm(emp, r)
  [Normed   Spec] ex r; test4_true$(emp, [()], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); ex r_7; test4_true$(emp, [()], r_7); Norm(emp, r_7)
  [Normed   Post] ex r_7; test4_true$(emp, [()], r_7); Norm(emp, r_7)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); ex r_7; test5_true$(emp, [b; n-1], r_7); Norm(emp, r_7)
  <:
  ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  
  unfold right
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); ex r_7; test5_true$(emp, [b; n-1], r_7); Norm(emp, r_7)
  <:
  ex r; Norm(r=0, r); Norm(emp, r) \/ ex r; test5_true$(emp, [b; n-1], r); Norm(emp, r); Norm(emp, r)
  
  norm, subsumption
  req emp; Norm(b=0, 0)
  <:
  ex r; req emp; Norm(r=0, r)
  
  (Norm pre) T => T ==> true
  (Norm post) b=0 => ex r. 0=r/\r=0 ==> true
  norm, subsumption
  ex r_7; req emp; test5_true(!b=1, [b; n-1], r_7); req emp; Norm(emp, r_7)
  <:
  ex r; req emp; Norm(r=0, r)
  
  FAIL, unequal length
  ex r_7; req emp; test5_true(!b=1, [b; n-1], r_7); req emp; Norm(emp, r_7)
  |=
  ex r; req emp; Norm(r=0, r)
  
  norm, subsumption
  ex r_7; req emp; test5_true(!b=1, [b; n-1], r_7); req emp; Norm(emp, r_7)
  <:
  ex r; req emp; test5_true(emp, [b; n-1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => ex r_7. T ==> true
  (Eff 0 post) !b=1 => ex r. r_7=r/\n-1=n-1/\b=b ==> true
  (Norm pre) r_7=r/\n-1=n-1/\b=b => T ==> true
  (Norm post) r_7=r/\n-1=n-1/\b=b => r_7=r ==> true
  
  ========== Function: test5_true ==========
  [Specification] ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  [Normed   Spec] ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); ex r_7; test5_true$(emp, [b; n-1], r_7); Norm(emp, r_7)
  [Normed   Post] Norm(b=0, 0) \/ ex r_7; test5_true$(!b=1, [b; n-1], r_7); Norm(emp, r_7)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); ex r_8; test6_true$(emp, [b; n-1-1], r_8); Norm(emp, r_8)
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
  ex r_8; req emp; test6_true(!b=1, [b; n-1-1], r_8); req emp; Norm(emp, r_8)
  <:
  req emp; Norm(emp, 0)
  
  FAIL, unequal length
  ex r_8; req emp; test6_true(!b=1, [b; n-1-1], r_8); req emp; Norm(emp, r_8)
  |=
  req emp; Norm(emp, 0)
  
  norm, subsumption
  ex r_8; req emp; test6_true(!b=1, [b; n-1-1], r_8); req emp; Norm(emp, r_8)
  <:
  ex r; req emp; test6_true(emp, [b; n-1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => ex r_8. T ==> true
  (Eff 0 post) !b=1 => ex r. r_8=r/\n-1-1=n-1/\b=b ==> false
  
  ========== Function: test6_true ==========
  [Specification] Norm(emp, 0) \/ ex r; test6_true$(emp, [b; n-1], r); Norm(emp, r)
  [Normed   Spec] Norm(emp, 0) \/ ex r; test6_true$(emp, [b; n-1], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); ex r_8; test6_true$(emp, [b; n-1-1], r_8); Norm(emp, r_8)
  [Normed   Post] Norm(b=0, 0) \/ Norm(!b=1, 0) \/ ex r_8; test6_true$(!b=1, [b; n-1-1], r_8); Norm(emp, r_8)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); ex r_7; test7_false$(emp, [b; n-1], r_7); Norm(emp, r_7)
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
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); ex r_7; test7_false$(emp, [b; n-1], r_7); Norm(emp, r_7)
  [Normed   Post] Norm(b=0, 0) \/ ex r_7; test7_false$(!b=1, [b; n-1], r_7); Norm(emp, r_7)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  <:
  Norm(emp, 0)
  
  unfold left
  Norm(emp, ()); ex r_7; Norm(r_7=0, r_7); Norm(emp, r_7) \/ Norm(emp, ()); ex r_7; test5_true$(emp, [b; n-1], r_7); Norm(emp, r_7); Norm(emp, r_7)
  <:
  Norm(emp, 0)
  
  apply ih
  Norm(emp, ()); ex r_7; Norm(r_7=0, r_7); Norm(emp, r_7)
  <:
  Norm(emp, 0)
  
  norm, subsumption
  ex r_7; req emp; Norm(r_7=0, r_7)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => ex r_7. T ==> true
  (Norm post) r_7=0 => r_7=0 ==> true
  
  ========== Function: test8_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  [Normed   Post] ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  <:
  Norm(emp, 1)
  
  unfold left
  Norm(emp, ()); ex r_7; Norm(r_7=0, r_7); Norm(emp, r_7) \/ Norm(emp, ()); ex r_7; test5_true$(emp, [b; n-1], r_7); Norm(emp, r_7); Norm(emp, r_7)
  <:
  Norm(emp, 1)
  
  apply ih
  Norm(emp, ()); ex r_7; Norm(r_7=0, r_7); Norm(emp, r_7)
  <:
  Norm(emp, 1)
  
  norm, subsumption
  ex r_7; req emp; Norm(r_7=0, r_7)
  <:
  req emp; Norm(emp, 1)
  
  (Norm pre) T => ex r_7. T ==> true
  (Norm post) r_7=0 => r_7=1 ==> false
  
  ========== Function: test9_false ==========
  [Specification] Norm(emp, 1)
  [Normed   Spec] Norm(emp, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  [Normed   Post] ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  <:
  Norm(emp, 0)
  
  unfold left
  Norm(emp, ()); ex r_7; Norm(r_7=0, r_7); Norm(emp, r_7) \/ Norm(emp, ()); ex r_7; test5_true$(emp, [b; n-1], r_7); Norm(emp, r_7); Norm(emp, r_7)
  <:
  Norm(emp, 0)
  
  norm, subsumption
  ex r_7; req emp; Norm(r_7=0, r_7)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => ex r_7. T ==> true
  (Norm post) r_7=0 => r_7=0 ==> true
  norm, subsumption
  ex r_7; req emp; test5_true(emp, [b; n-1], r_7); req emp; Norm(emp, r_7)
  <:
  req emp; Norm(emp, 0)
  
  FAIL, unequal length
  ex r_7; req emp; test5_true(emp, [b; n-1], r_7); req emp; Norm(emp, r_7)
  |=
  req emp; Norm(emp, 0)
  
  
  ========== Function: test10_false ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  [Normed   Post] ex r_7; test5_true$(emp, [b; n], r_7); Norm(emp, r_7)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex f6; g$(emp, [x], f6); ex f7; f$(emp, [f6], f7)
  <:
  ex r_g; g$(emp, [x], r_g); ex r_f; f$(emp, [r_g], r_f); Norm(emp, r_f)
  
  norm, subsumption
  ex f6; req emp; g(emp, [x], f6); ex f7; req emp; f(emp, [f6], f7); req emp; Norm(emp, f7)
  <:
  ex r_g; req emp; g(emp, [x], r_g); ex r_f; req emp; f(emp, [r_g], r_f); req emp; Norm(emp, r_f)
  
  (Eff 0 pre) T => ex f6. T ==> true
  (Eff 0 post) T => ex r_g. f6=r_g/\x=x ==> true
  (Eff 1 pre) f6=r_g/\x=x => ex f7. T ==> true
  (Eff 1 post) f6=r_g/\x=x => ex r_f. f7=r_f/\f6=r_g ==> true
  (Norm pre) f6=r_g/\x=x/\f7=r_f/\f6=r_g/\f6=r_g/\x=x => T ==> true
  (Norm post) f6=r_g/\x=x/\f7=r_f/\f6=r_g/\f6=r_g/\x=x => f7=r_f ==> true
  
  ========== Function: compose_true ==========
  [Specification] ex r_g; g$(emp, [x], r_g); ex r_f; f$(emp, [r_g], r_f); Norm(emp, r_f)
  [Normed   Spec] ex r_g; g$(emp, [x], r_g); ex r_f; f$(emp, [r_g], r_f); Norm(emp, r_f)
  
  [Raw Post Spec] Norm(emp, ()); ex f6; g$(emp, [x], f6); ex f7; f$(emp, [f6], f7)
  [Normed   Post] ex f6; g$(emp, [x], f6); ex f7; f$(emp, [f6], f7); Norm(emp, f7)
  
  [Entail  Check] true
  ============================================
  
  before tactics
  Norm(emp, ()); ex f6; g$(emp, [x], f6); ex f7; f$(emp, [f6], f7)
  <:
  ex r_g r_f; g$(emp, [x], r_g); f$(emp, [r_g], r_f); Norm(emp, r_f)
  
  norm, subsumption
  ex f6; req emp; g(emp, [x], f6); ex f7; req emp; f(emp, [f6], f7); req emp; Norm(emp, f7)
  <:
  ex r_g r_f; req emp; g(emp, [x], r_g); req emp; f(emp, [r_g], r_f); req emp; Norm(emp, r_f)
  
  (Eff 0 pre) T => ex f6. T ==> true
  (Eff 0 post) T => ex r_g,r_f. f6=r_g/\x=x ==> true
  (Eff 1 pre) f6=r_g/\x=x => ex f7. T ==> true
  (Eff 1 post) f6=r_g/\x=x => f7=r_f/\f6=r_g ==> false
  
  ========== Function: compose_exists_false ==========
  [Specification] ex r_g r_f; g$(emp, [x], r_g); f$(emp, [r_g], r_f); Norm(emp, r_f)
  [Normed   Spec] ex r_g r_f; g$(emp, [x], r_g); f$(emp, [r_g], r_f); Norm(emp, r_f)
  
  [Raw Post Spec] Norm(emp, ()); ex f6; g$(emp, [x], f6); ex f7; f$(emp, [f6], f7)
  [Normed   Post] ex f6; g$(emp, [x], f6); ex f7; f$(emp, [f6], f7); Norm(emp, f7)
  
  [Entail  Check] false
  ====================================================
  
