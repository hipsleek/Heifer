
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
  Norm(emp, ()); ex f47; Norm(f47->0, f47); Norm(emp, f47)
  <:
  ex i; Norm(i->0, i)
  
  norm, subsumption
  ex f47; req emp; Norm(f47->0, f47)
  <:
  ex i; req emp; Norm(i->0, i)
  
  (Norm pre) T => ex f47. T ==> true
  (Norm post) T => ex i. f47=i/\0=0 ==> true
  
  ========== Function: test4_true ==========
  [Specification] ex i; Norm(i->0, i)
  [Normed   Spec] ex i; Norm(i->0, i)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); Norm(emp, f47)
  [Normed   Post] ex f47; Norm(f47->0, f47)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex i_48; req f47->i_48; Norm(f47->i_48, i_48); Norm(emp, i_48+1)
  <:
  ex i; Norm(i->0, 1)
  
  norm, subsumption
  ex f47 i_48; req emp; Norm(f47->i_48 /\ i_48=0, i_48+1)
  <:
  ex i; req emp; Norm(i->0, 1)
  
  (Norm pre) T => ex f47,i_48. T ==> true
  (Norm post) i_48=0 => ex i. i_48+1=1/\0=i_48 ==> true
  
  ========== Function: test5_true ==========
  [Specification] ex i; Norm(i->0, 1)
  [Normed   Spec] ex i; Norm(i->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex i_48; req f47->i_48; Norm(f47->i_48, i_48); Norm(emp, i_48+1)
  [Normed   Post] ex f47 i_48; Norm(f47->i_48 /\ i_48=0, i_48+1)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex i_48; req f47->i_48; Norm(f47->i_48, i_48); Norm(emp, i_48+1); ex f49; req f47->f49; Norm(f47->i_48+1, ()); ex i_50; req f47->i_50; Norm(f47->i_50, i_50)
  <:
  ex i; Norm(i->1, 1)
  
  norm, subsumption
  ex f47 i_48 f49 i_50; req i_48=f49/\i_48+1=i_50; Norm(f47->i_50 /\ i_48=0/\f49=i_48/\i_50=i_48+1, i_50)
  <:
  ex i; req emp; Norm(i->1, 1)
  
  (Norm pre) T => ex f47,i_48,f49,i_50. i_48=f49/\i_48+1=i_50 ==> true
  (Norm post) i_48=0/\f49=i_48/\i_50=i_48+1/\i_48=f49/\i_48+1=i_50 => ex i. i_50=1/\1=i_50 ==> true
  
  ========== Function: test6_true ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex i_48; req f47->i_48; Norm(f47->i_48, i_48); Norm(emp, i_48+1); ex f49; req f47->f49; Norm(f47->i_48+1, ()); ex i_50; req f47->i_50; Norm(f47->i_50, i_50)
  [Normed   Post] ex f47 i_48 f49 i_50; req i_48=f49/\i_48+1=i_50; Norm(f47->i_50 /\ i_48=0/\f49=i_48/\i_50=i_48+1, i_50)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex i_48; req f47->i_48; Norm(f47->i_48, i_48); Norm(emp, i_48+2); ex f49; req f47->f49; Norm(f47->i_48+2, ()); ex i_50; req f47->i_50; Norm(f47->i_50, i_50)
  <:
  ex i; Norm(i->1, 1)
  
  norm, subsumption
  ex f47 i_48 f49 i_50; req i_48=f49/\i_48+2=i_50; Norm(f47->i_50 /\ i_48=0/\f49=i_48/\i_50=i_48+2, i_50)
  <:
  ex i; req emp; Norm(i->1, 1)
  
  (Norm pre) T => ex f47,i_48,f49,i_50. i_48=f49/\i_48+2=i_50 ==> true
  (Norm post) i_48=0/\f49=i_48/\i_50=i_48+2/\i_48=f49/\i_48+2=i_50 => ex i. i_50=1/\1=i_50 ==> false
  
  ========== Function: test23_false ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex i_48; req f47->i_48; Norm(f47->i_48, i_48); Norm(emp, i_48+2); ex f49; req f47->f49; Norm(f47->i_48+2, ()); ex i_50; req f47->i_50; Norm(f47->i_50, i_50)
  [Normed   Post] ex f47 i_48 f49 i_50; req i_48=f49/\i_48+2=i_50; Norm(f47->i_50 /\ i_48=0/\f49=i_48/\i_50=i_48+2, i_50)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex res_47; Eff(emp, [], res_47); Norm(emp, res_47); Norm(emp, 1)
  <:
  ex r; Eff(emp, [], r)
  
  norm, subsumption
  ex res_47; req emp; Eff(emp, [], res_47); req emp; Norm(emp, 1)
  <:
  ex r; req emp; Eff(emp, [], r); ex n_55; req emp; Norm(emp, n_55)
  
  (Eff 0 pre) T => ex res_47. T ==> true
  (Eff 0 post) T => ex r. res_47=r ==> true
  (Norm pre) res_47=r => T ==> true
  (Norm post) res_47=r => ex n_55. 1=n_55 ==> true
  
  ========== Function: test19_true ==========
  [Specification] ex r; Eff(emp, [], r)
  [Normed   Spec] ex r; Eff(emp, [], r); ex n_49; Norm(emp, n_49)
  
  [Raw Post Spec] Norm(emp, ()); ex res_47; Eff(emp, [], res_47); Norm(emp, res_47); Norm(emp, 1)
  [Normed   Post] ex res_47; Eff(emp, [], res_47); Norm(emp, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex res_47; Eff(emp, [], res_47); Norm(emp, res_47); Norm(emp, res_47)
  <:
  Eff(emp, [], ())
  
  norm, subsumption
  ex res_47; req emp; Eff(emp, [], res_47); req emp; Norm(emp, res_47)
  <:
  req emp; Eff(emp, [], ()); ex n_55; req emp; Norm(emp, n_55)
  
  (Eff 0 pre) T => ex res_47. T ==> true
  (Eff 0 post) T => res_47=() ==> false
  
  ========== Function: test25_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); ex n_49; Norm(emp, n_49)
  
  [Raw Post Spec] Norm(emp, ()); ex res_47; Eff(emp, [], res_47); Norm(emp, res_47); Norm(emp, res_47)
  [Normed   Post] ex res_47; Eff(emp, [], res_47); Norm(emp, res_47)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex res_47; Eff(emp, [], res_47); Norm(emp, res_47); Norm(emp, 1)
  <:
  Eff(emp, [], ())
  
  norm, subsumption
  ex res_47; req emp; Eff(emp, [], res_47); req emp; Norm(emp, 1)
  <:
  req emp; Eff(emp, [], ()); ex n_55; req emp; Norm(emp, n_55)
  
  (Eff 0 pre) T => ex res_47. T ==> true
  (Eff 0 post) T => res_47=() ==> false
  
  ========== Function: test12_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); ex n_49; Norm(emp, n_49)
  
  [Raw Post Spec] Norm(emp, ()); ex res_47; Eff(emp, [], res_47); Norm(emp, res_47); Norm(emp, 1)
  [Normed   Post] ex res_47; Eff(emp, [], res_47); Norm(emp, 1)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); ex i_49; req f47->i_49; Norm(f47->i_49, i_49); Norm(emp, i_49+1); ex f50; req f47->f50; Norm(f47->i_49+1, ()); Norm(emp, res_48)
  <:
  ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f47 res_48; req emp; Eff(f47->0, [], res_48); ex i_49 f50; req f47->i_49 /\ i_49=f50; Norm(f47->i_49+1 /\ f50=i_49, res_48)
  <:
  ex i ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f47,res_48. T ==> true
  (Eff 0 post) T => ex i,ret. res_48=ret/\0=0 ==> true
  (Norm pre) res_48=ret/\0=0 => ex i_49,f50. i_49=z/\i_49=f50 ==> true
  (Norm post) f50=i_49/\i_49=z/\i_49=f50/\res_48=ret/\0=0 => res_48=ret/\z+1=i_49+1 ==> true
  
  ========== Function: test21_true ==========
  [Specification] ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); ex i_49; req f47->i_49; Norm(f47->i_49, i_49); Norm(emp, i_49+1); ex f50; req f47->f50; Norm(f47->i_49+1, ()); Norm(emp, res_48)
  [Normed   Post] ex f47 res_48; Eff(f47->0, [], res_48); ex i_49 f50; req f47->i_49 /\ i_49=f50; Norm(f47->i_49+1 /\ f50=i_49, res_48)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); ex i_49; req f47->i_49; Norm(f47->i_49, i_49); Norm(emp, i_49+1); ex f50; req f47->f50; Norm(f47->i_49+1, ()); Norm(emp, res_48)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f47 res_48; req emp; Eff(f47->0, [], res_48); ex i_49 f50; req f47->i_49 /\ i_49=f50; Norm(f47->i_49+1 /\ f50=i_49, res_48)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f47,res_48. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_48=ret/\0=0 ==> true
  (Norm pre) res_48=ret/\0=0 => ex i_49,f50. i_49=z/\i_49=f50 ==> true
  (Norm post) f50=i_49/\i_49=z/\i_49=f50/\res_48=ret/\0=0 => res_48=ret/\z+1=i_49+1 ==> true
  
  ========== Function: test0_true ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); ex i_49; req f47->i_49; Norm(f47->i_49, i_49); Norm(emp, i_49+1); ex f50; req f47->f50; Norm(f47->i_49+1, ()); Norm(emp, res_48)
  [Normed   Post] ex f47 res_48; Eff(f47->0, [], res_48); ex i_49 f50; req f47->i_49 /\ i_49=f50; Norm(f47->i_49+1 /\ f50=i_49, res_48)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); ex i_49; req f47->i_49; Norm(f47->i_49, i_49); Norm(emp, i_49+1); ex f50; req f47->f50; Norm(f47->i_49+1, ()); ex i_51; req f47->i_51; Norm(f47->i_51, i_51)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f47 res_48; req emp; Eff(f47->0, [], res_48); ex i_49 f50 i_51; req f47->i_49 /\ i_49=f50/\i_49+1=i_51; Norm(f47->i_51 /\ f50=i_49/\i_51=i_49+1, i_51)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f47,res_48. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_48=ret/\0=0 ==> true
  (Norm pre) res_48=ret/\0=0 => ex i_49,f50,i_51. i_49=z/\i_49=f50/\i_49+1=i_51 ==> true
  (Norm post) f50=i_49/\i_51=i_49+1/\i_49=z/\i_49=f50/\i_49+1=i_51/\res_48=ret/\0=0 => i_51=ret/\z+1=i_51 ==> false
  
  ========== Function: test1_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); ex i_49; req f47->i_49; Norm(f47->i_49, i_49); Norm(emp, i_49+1); ex f50; req f47->f50; Norm(f47->i_49+1, ()); ex i_51; req f47->i_51; Norm(f47->i_51, i_51)
  [Normed   Post] ex f47 res_48; Eff(f47->0, [], res_48); ex i_49 f50 i_51; req f47->i_49 /\ i_49=f50/\i_49+1=i_51; Norm(f47->i_51 /\ f50=i_49/\i_51=i_49+1, i_51)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, res_48)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f47 res_48; req emp; Eff(f47->0, [], res_48); req emp; Norm(emp, res_48)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f47,res_48. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_48=ret/\0=0 ==> true
  (Norm pre) i>0/\res_48=ret/\0=0 => T ==> true
  
  ========== Function: test2_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); Norm(emp, res_48)
  [Normed   Post] ex f47 res_48; Eff(f47->0, [], res_48); Norm(emp, res_48)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); ex i_49; req f47->i_49; Norm(f47->i_49, i_49); Norm(emp, i_49+2); ex f50; req f47->f50; Norm(f47->i_49+2, ()); Norm(emp, res_48)
  <:
  ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  norm, subsumption
  ex f47 res_48; req emp; Eff(f47->0, [], res_48); ex i_49 f50; req f47->i_49 /\ i_49=f50; Norm(f47->i_49+2 /\ f50=i_49, res_48)
  <:
  ex i z ret; req emp; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  (Eff 0 pre) T => ex f47,res_48. T ==> true
  (Eff 0 post) T => ex i,z,ret. res_48=ret/\0=0 ==> true
  (Norm pre) res_48=ret/\0=0 => ex i_49,f50. i_49=z/\i_49=f50 ==> true
  (Norm post) f50=i_49/\i_49=z/\i_49=f50/\res_48=ret/\0=0 => res_48=ret/\z+1=i_49+2 ==> false
  
  ========== Function: test3_false ==========
  [Specification] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i z ret; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex res_48; Eff(emp, [], res_48); Norm(emp, res_48); ex i_49; req f47->i_49; Norm(f47->i_49, i_49); Norm(emp, i_49+2); ex f50; req f47->f50; Norm(f47->i_49+2, ()); Norm(emp, res_48)
  [Normed   Post] ex f47 res_48; Eff(f47->0, [], res_48); ex i_49 f50; req f47->i_49 /\ i_49=f50; Norm(f47->i_49+2 /\ f50=i_49, res_48)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex f48; Norm(f48->1, f48); Norm(emp, 1)
  <:
  ex a b; Norm(a->0*b->1, 1)
  
  norm, subsumption
  ex f47 f48; req emp; Norm(f47->0*f48->1, 1)
  <:
  ex a b; req emp; Norm(a->0*b->1, 1)
  
  (Norm pre) T => ex f47,f48. T ==> true
  (Norm post) T => ex a,b. 1=1/\1=1/\0=0 ==> true
  
  ========== Function: test13_true ==========
  [Specification] ex a b; Norm(a->0*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->0*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex f48; Norm(f48->1, f48); Norm(emp, 1)
  [Normed   Post] ex f47 f48; Norm(f47->0*f48->1, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex f48; Norm(f48->2, f48); Norm(emp, 1)
  <:
  ex a b; Norm(a->1+1*b->0, 1)
  
  norm, subsumption
  ex f47 f48; req emp; Norm(f47->0*f48->2, 1)
  <:
  ex a b; req emp; Norm(a->1+1*b->0, 1)
  
  (Norm pre) T => ex f47,f48. T ==> true
  (Norm post) T => ex a,b. 1=1/\0=2/\1+1=0 ==> false
  (Norm post) T => ex a,b. 1=1/\0=0/\1+1=2 ==> true
  
  ========== Function: test18_true ==========
  [Specification] ex a b; Norm(a->1+1*b->0, 1)
  [Normed   Spec] ex a b; Norm(a->1+1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex f48; Norm(f48->2, f48); Norm(emp, 1)
  [Normed   Post] ex f47 f48; Norm(f47->0*f48->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); req i->1; Norm(i->1, ()); ex f47; Norm(f47->2, f47); Norm(emp, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  norm, subsumption
  ex f47; req i->1; Norm(i->1*f47->2, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  (Norm pre) T => ex f47. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\2=2/\1=1 ==> true
  
  ========== Function: test20_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); req i->1; Norm(i->1, ()); ex f47; Norm(f47->2, f47); Norm(emp, 1)
  [Normed   Post] ex f47; req i->1; Norm(i->1*f47->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); req i->1; Norm(i->1, ()); ex f47; Norm(f47->2, f47); req f47->2; Norm(f47->2, ()); Norm(emp, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  norm, subsumption
  ex f47; req i->1; Norm(i->1*f47->2, 1)
  <:
  ex b; req i->1; Norm(i->1*b->2, 1)
  
  (Norm pre) T => ex f47. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\2=2/\1=1 ==> true
  
  ========== Function: test21_true ==========
  [Specification] ex b; req i->1; Norm(i->1*b->2, 1)
  [Normed   Spec] ex b; req i->1; Norm(i->1*b->2, 1)
  
  [Raw Post Spec] Norm(emp, ()); req i->1; Norm(i->1, ()); ex f47; Norm(f47->2, f47); req f47->2; Norm(f47->2, ()); Norm(emp, 1)
  [Normed   Post] ex f47; req i->1; Norm(i->1*f47->2, 1)
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->2, f47); ex j_48; req f47->j_48; Norm(f47->j_48, j_48); req f47->j_48; Norm(f47->j_48, ())
  <:
  ex i a; Norm(i->a, ())
  
  norm, subsumption
  ex f47 j_48; req emp; Norm(f47->j_48 /\ j_48=2, ())
  <:
  ex i a; req emp; Norm(i->a, ())
  
  (Norm pre) T => ex f47,j_48. T ==> true
  (Norm post) j_48=2 => ex i,a. ()=()/\a=j_48 ==> true
  
  ========== Function: test22_true ==========
  [Specification] ex i a; Norm(i->a, ())
  [Normed   Spec] ex i a; Norm(i->a, ())
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->2, f47); ex j_48; req f47->j_48; Norm(f47->j_48, j_48); req f47->j_48; Norm(f47->j_48, ())
  [Normed   Post] ex f47 j_48; Norm(f47->j_48 /\ j_48=2, ())
  
  [Entail  Check] true
  ===========================================
  
  before tactics
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex f48; Norm(f48->1, f48); Norm(emp, 1)
  <:
  ex a b; Norm(a->1*b->1, 1)
  
  norm, subsumption
  ex f47 f48; req emp; Norm(f47->0*f48->1, 1)
  <:
  ex a b; req emp; Norm(a->1*b->1, 1)
  
  (Norm pre) T => ex f47,f48. T ==> true
  (Norm post) T => ex a,b. 1=1/\1=1/\1=0 ==> false
  (Norm post) T => ex a,b. 1=1/\1=0/\1=1 ==> false
  
  ========== Function: test14_false ==========
  [Specification] ex a b; Norm(a->1*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->1*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex f48; Norm(f48->1, f48); Norm(emp, 1)
  [Normed   Post] ex f47 f48; Norm(f47->0*f48->1, 1)
  
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
  Norm(emp, ()); ex f47; Norm(f47->0, f47); Norm(emp, 1)
  <:
  ex a; req a->1; Norm(a->1, 1)
  
  norm, subsumption
  ex f47; req emp; Norm(f47->0, 1)
  <:
  ex a; req a->1; Norm(a->1, 1)
  
  (Norm pre) a>0 => ex f47. T ==> true
  (Norm post) a>0 => 1=1/\1=0 ==> false
  
  ========== Function: test16_false ==========
  [Specification] ex a; req a->1; Norm(a->1, 1)
  [Normed   Spec] ex a; req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); Norm(emp, 1)
  [Normed   Post] ex f47; Norm(f47->0, 1)
  
  [Entail  Check] false
  ============================================
  
  before tactics
  Norm(emp, ()); req a->1; Norm(a->1, ()); ex f47; Norm(f47->0, f47); Norm(emp, 1)
  <:
  ex b; req a->1; Norm(a->1*b->0, 1)
  
  norm, subsumption
  ex f47; req a->1; Norm(a->1*f47->0, 1)
  <:
  ex b; req a->1; Norm(a->1*b->0, 1)
  
  (Norm pre) T => ex f47. 1=1 ==> true
  (Norm post) 1=1 => ex b. 1=1/\0=0/\1=1 ==> true
  
  ========== Function: test17_true ==========
  [Specification] ex b; req a->1; Norm(a->1*b->0, 1)
  [Normed   Spec] ex b; req a->1; Norm(a->1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); req a->1; Norm(a->1, ()); ex f47; Norm(f47->0, f47); Norm(emp, 1)
  [Normed   Post] ex f47; req a->1; Norm(a->1*f47->0, 1)
  
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
  Norm(emp, ()); ex f47; Norm(f47->0, f47); ex f48; Norm(f48->0, f48); ex res_49; E(emp, [], res_49); Norm(emp, res_49); ex i_50; req f47->i_50; Norm(f47->i_50, i_50); Norm(emp, i_50+1); ex f51; req f47->f51; Norm(f47->i_50+1, ()); ex j_52; req f48->j_52; Norm(f48->j_52, j_52); Norm(emp, j_52+1); ex f53; req f48->f53; Norm(f48->j_52+1, ()); Norm(emp, res_49)
  <:
  ex i j z1 z2 ret; E(i->0*j->0, [], ret); req i->z1*j->z2; Norm(i->z1+1*j->z2+1, ret)
  
  norm, subsumption
  ex f47 f48 res_49; req emp; E(f47->0*f48->0, [], res_49); ex i_50 f51 j_52 f53; req f47->i_50*f48->j_52 /\ i_50=f51/\j_52=f53; Norm(f47->i_50+1*f48->j_52+1 /\ f51=i_50/\f53=j_52, res_49)
  <:
  ex i j z1 z2 ret; req emp; E(i->0*j->0, [], ret); req i->z1*j->z2*emp; Norm(i->z1+1*j->z2+1, ret)
  
  (Eff 0 pre) T => ex f47,f48,res_49. T ==> true
  (Eff 0 post) T => ex i,j,z1,z2,ret. res_49=ret/\0=0/\0=0 ==> true
  (Norm pre) res_49=ret/\0=0/\0=0 => ex i_50,f51,j_52,f53. j_52=z2/\i_50=z1/\i_50=f51/\j_52=f53 ==> true
  (Norm post) f51=i_50/\f53=j_52/\j_52=z2/\i_50=z1/\i_50=f51/\j_52=f53/\res_49=ret/\0=0/\0=0 => res_49=ret/\z2+1=j_52+1/\z1+1=i_50+1 ==> true
  
  ========== Function: two_locations_true ==========
  [Specification] ex i j z1 z2 ret; E(i->0*j->0, [], ret); req i->z1*j->z2; Norm(i->z1+1*j->z2+1, ret)
  [Normed   Spec] ex i j z1 z2 ret; E(i->0*j->0, [], ret); req i->z1*j->z2*emp; Norm(i->z1+1*j->z2+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f47; Norm(f47->0, f47); ex f48; Norm(f48->0, f48); ex res_49; E(emp, [], res_49); Norm(emp, res_49); ex i_50; req f47->i_50; Norm(f47->i_50, i_50); Norm(emp, i_50+1); ex f51; req f47->f51; Norm(f47->i_50+1, ()); ex j_52; req f48->j_52; Norm(f48->j_52, j_52); Norm(emp, j_52+1); ex f53; req f48->f53; Norm(f48->j_52+1, ()); Norm(emp, res_49)
  [Normed   Post] ex f47 f48 res_49; E(f47->0*f48->0, [], res_49); ex i_50 f51 j_52 f53; req f47->i_50*f48->j_52 /\ i_50=f51/\j_52=f53; Norm(f47->i_50+1*f48->j_52+1 /\ f51=i_50/\f53=j_52, res_49)
  
  [Entail  Check] true
  ==================================================
  

  $ hip test_ho.ml 2>&1 | grep 'Function\|Entail.*Check' | ./check.py
  TESTS FAILED
  ========== Function: test1_true ==========
  ========== Function: test2_true ==========
  ========== Function: test3_true ==========
  ========== Function: test6_true ==========

  $ hip test_ho.ml 2>&1 | ./sanitize.sh
  before tactics
  Norm(emp, ()); ex f4; f$(emp, [1], f4)
  <:
  ex r; f$(emp, [1], r); Norm(emp, r)
  
  norm, subsumption
  ex f4; req emp; f(emp, [1], f4); ex n_10; req emp; Norm(emp, n_10)
  <:
  ex r; req emp; f(emp, [1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => ex f4. T ==> true
  (Eff 0 post) T => ex r. f4=r/\1=1 ==> true
  (Norm pre) f4=r/\1=1 => ex n_10. T ==> true
  (Norm post) f4=r/\1=1 => n_10=r ==> false
  
  ========== Function: test1_true ==========
  [Specification] ex r; f$(emp, [1], r); Norm(emp, r)
  [Normed   Spec] ex r; f$(emp, [1], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); ex f4; f$(emp, [1], f4)
  [Normed   Post] ex f4; f$(emp, [1], f4); ex n_8; Norm(emp, n_8)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f4; f$(emp, [1], f4); ex f5; g$(emp, [1], f5)
  <:
  ex r; ex s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  
  norm, subsumption
  ex f4; req emp; f(emp, [1], f4); ex f5; req emp; g(emp, [1], f5); ex n_14; req emp; Norm(emp, n_14)
  <:
  ex r s; req emp; f(emp, [1], r); req emp; g(emp, [2], s); req emp; Norm(emp, s)
  
  (Eff 0 pre) T => ex f4. T ==> true
  (Eff 0 post) T => ex r,s. f4=r/\1=1 ==> true
  (Eff 1 pre) f4=r/\1=1 => ex f5. T ==> true
  (Eff 1 post) f4=r/\1=1 => f5=s/\1=2 ==> false
  
  ========== Function: test2_true ==========
  [Specification] ex r; ex s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  [Normed   Spec] ex r s; f$(emp, [1], r); g$(emp, [2], s); Norm(emp, s)
  
  [Raw Post Spec] Norm(emp, ()); ex f4; f$(emp, [1], f4); ex f5; g$(emp, [1], f5)
  [Normed   Post] ex f4; f$(emp, [1], f4); ex f5; g$(emp, [1], f5); ex n_11; Norm(emp, n_11)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); ex f4; f$(emp, [1], f4); ex f5; g$(emp, [f4], f5)
  <:
  ex r; ex s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  
  norm, subsumption
  ex f4; req emp; f(emp, [1], f4); ex f5; req emp; g(emp, [f4], f5); ex n_14; req emp; Norm(emp, n_14)
  <:
  ex r s; req emp; f(emp, [1], r); req emp; g(emp, [r], s); req emp; Norm(emp, s)
  
  (Eff 0 pre) T => ex f4. T ==> true
  (Eff 0 post) T => ex r,s. f4=r/\1=1 ==> true
  (Eff 1 pre) f4=r/\1=1 => ex f5. T ==> true
  (Eff 1 post) f4=r/\1=1 => f5=s/\f4=r ==> false
  
  ========== Function: test3_true ==========
  [Specification] ex r; ex s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  [Normed   Spec] ex r s; f$(emp, [1], r); g$(emp, [r], s); Norm(emp, s)
  
  [Raw Post Spec] Norm(emp, ()); ex f4; f$(emp, [1], f4); ex f5; g$(emp, [f4], f5)
  [Normed   Post] ex f4; f$(emp, [1], f4); ex f5; g$(emp, [f4], f5); ex n_11; Norm(emp, n_11)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); test4_true$(emp, [()], r_6); Norm(emp, r_6)
  <:
  ex r; test4_true$(emp, [()], r); Norm(emp, r)
  
  norm, subsumption
  req emp; test4_true(emp, [()], r_6); req emp; Norm(emp, r_6)
  <:
  ex r; req emp; test4_true(emp, [()], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => T ==> true
  (Eff 0 post) T => ex r. r_6=r/\()=() ==> true
  (Norm pre) r_6=r/\()=() => T ==> true
  (Norm post) r_6=r/\()=() => r_6=r ==> true
  
  ========== Function: test4_true ==========
  [Specification] ex r; test4_true$(emp, [()], r); Norm(emp, r)
  [Normed   Spec] ex r; test4_true$(emp, [()], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); test4_true$(emp, [()], r_6); Norm(emp, r_6)
  [Normed   Post] test4_true$(emp, [()], r_6); Norm(emp, r_6)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test5_true$(emp, [b; n-1], r_6); Norm(emp, r_6)
  <:
  ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  
  unfold right
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test5_true$(emp, [b; n-1], r_6); Norm(emp, r_6)
  <:
  ex r; Norm(r=0, r); Norm(emp, r) \/ ex r; test5_true$(emp, [b; n-1], r); Norm(emp, r); Norm(emp, r)
  
  norm, subsumption
  req emp; Norm(b=0, 0)
  <:
  ex r; req emp; Norm(r=0, r)
  
  (Norm pre) T => T ==> true
  (Norm post) b=0 => ex r. 0=r/\r=0 ==> true
  norm, subsumption
  req emp; test5_true(!b=1, [b; n-1], r_6); req emp; Norm(emp, r_6)
  <:
  ex r; req emp; Norm(r=0, r)
  
  FAIL, unequal length
  req emp; test5_true(!b=1, [b; n-1], r_6); req emp; Norm(emp, r_6)
  |=
  ex r; req emp; Norm(r=0, r)
  
  norm, subsumption
  req emp; test5_true(!b=1, [b; n-1], r_6); req emp; Norm(emp, r_6)
  <:
  ex r; req emp; test5_true(emp, [b; n-1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => T ==> true
  (Eff 0 post) !b=1 => ex r. r_6=r/\n-1=n-1/\b=b ==> true
  (Norm pre) r_6=r/\n-1=n-1/\b=b => T ==> true
  (Norm post) r_6=r/\n-1=n-1/\b=b => r_6=r ==> true
  
  ========== Function: test5_true ==========
  [Specification] ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  [Normed   Spec] ex r; test5_true$(emp, [b; n], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test5_true$(emp, [b; n-1], r_6); Norm(emp, r_6)
  [Normed   Post] Norm(b=0, 0) \/ test5_true$(!b=1, [b; n-1], r_6); Norm(emp, r_6)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test6_true$(emp, [b; n-1-1], r_7); Norm(emp, r_7)
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
  req emp; test6_true(!b=1, [b; n-1-1], r_7); req emp; Norm(emp, r_7)
  <:
  req emp; Norm(emp, 0)
  
  FAIL, unequal length
  req emp; test6_true(!b=1, [b; n-1-1], r_7); req emp; Norm(emp, r_7)
  |=
  req emp; Norm(emp, 0)
  
  norm, subsumption
  req emp; test6_true(!b=1, [b; n-1-1], r_7); req emp; Norm(emp, r_7)
  <:
  ex r; req emp; test6_true(emp, [b; n-1], r); req emp; Norm(emp, r)
  
  (Eff 0 pre) T => T ==> true
  (Eff 0 post) !b=1 => ex r. r_7=r/\n-1-1=n-1/\b=b ==> false
  
  ========== Function: test6_true ==========
  [Specification] Norm(emp, 0) \/ ex r; test6_true$(emp, [b; n-1], r); Norm(emp, r)
  [Normed   Spec] Norm(emp, 0) \/ ex r; test6_true$(emp, [b; n-1], r); Norm(emp, r)
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test6_true$(emp, [b; n-1-1], r_7); Norm(emp, r_7)
  [Normed   Post] Norm(b=0, 0) \/ Norm(!b=1, 0) \/ test6_true$(!b=1, [b; n-1-1], r_7); Norm(emp, r_7)
  
  [Entail  Check] false
  ==========================================
  
  before tactics
  Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test7_false$(emp, [b; n-1], r_6); Norm(emp, r_6)
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
  
  [Raw Post Spec] Norm(emp, ()); Norm(b=0, ()); Norm(emp, 0) \/ Norm(emp, ()); Norm(!b=1, ()); Norm(emp, n-1); test7_false$(emp, [b; n-1], r_6); Norm(emp, r_6)
  [Normed   Post] Norm(b=0, 0) \/ test7_false$(!b=1, [b; n-1], r_6); Norm(emp, r_6)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  <:
  Norm(emp, 0)
  
  unfold left
  Norm(emp, ()); Norm(r_6=0, r_6); Norm(emp, r_6) \/ Norm(emp, ()); test5_true$(emp, [b; n-1], r_6); Norm(emp, r_6); Norm(emp, r_6)
  <:
  Norm(emp, 0)
  
  apply ih
  Norm(emp, ()); Norm(r_6=0, r_6); Norm(emp, r_6)
  <:
  Norm(emp, 0)
  
  norm, subsumption
  req emp; Norm(r_6=0, r_6)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => T ==> true
  (Norm post) r_6=0 => r_6=0 ==> true
  
  ========== Function: test8_true ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  [Normed   Post] test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  
  [Entail  Check] true
  ==========================================
  
  before tactics
  Norm(emp, ()); test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  <:
  Norm(emp, 1)
  
  unfold left
  Norm(emp, ()); Norm(r_6=0, r_6); Norm(emp, r_6) \/ Norm(emp, ()); test5_true$(emp, [b; n-1], r_6); Norm(emp, r_6); Norm(emp, r_6)
  <:
  Norm(emp, 1)
  
  apply ih
  Norm(emp, ()); Norm(r_6=0, r_6); Norm(emp, r_6)
  <:
  Norm(emp, 1)
  
  norm, subsumption
  req emp; Norm(r_6=0, r_6)
  <:
  req emp; Norm(emp, 1)
  
  (Norm pre) T => T ==> true
  (Norm post) r_6=0 => r_6=1 ==> false
  
  ========== Function: test9_false ==========
  [Specification] Norm(emp, 1)
  [Normed   Spec] Norm(emp, 1)
  
  [Raw Post Spec] Norm(emp, ()); test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  [Normed   Post] test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  
  [Entail  Check] false
  ===========================================
  
  before tactics
  Norm(emp, ()); test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  <:
  Norm(emp, 0)
  
  unfold left
  Norm(emp, ()); Norm(r_6=0, r_6); Norm(emp, r_6) \/ Norm(emp, ()); test5_true$(emp, [b; n-1], r_6); Norm(emp, r_6); Norm(emp, r_6)
  <:
  Norm(emp, 0)
  
  norm, subsumption
  req emp; Norm(r_6=0, r_6)
  <:
  req emp; Norm(emp, 0)
  
  (Norm pre) T => T ==> true
  (Norm post) r_6=0 => r_6=0 ==> true
  norm, subsumption
  req emp; test5_true(emp, [b; n-1], r_6); req emp; Norm(emp, r_6)
  <:
  req emp; Norm(emp, 0)
  
  FAIL, unequal length
  req emp; test5_true(emp, [b; n-1], r_6); req emp; Norm(emp, r_6)
  |=
  req emp; Norm(emp, 0)
  
  
  ========== Function: test10_false ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  [Normed   Post] test5_true$(emp, [b; n], r_6); Norm(emp, r_6)
  
  [Entail  Check] false
  ============================================
  
