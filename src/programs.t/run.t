
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
  ========== Function: test_true ==========
  [Entail  Check] true
  ========== Function: test13_true ==========
  [Entail  Check] true
  ========== Function: test18_true ==========
  ========== Function: test15_true ==========
  ========== Function: test17_true ==========

  $ hip test_new_entail.ml 2>&1 | grep 'Function\|Entail' | grep false
  ========== Function: test7_false ==========
  [Entail  Check] false
  ========== Function: test8_false ==========
  [Entail  Check] false
  ========== Function: test12_false ==========
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
  
  ex f29 i. T=>T // norm pre
  /\ T=>0=0 // norm post
  /\ f29=i // norm res eq
  z3: valid
  
  ========== Function: test4_true ==========
  [Specification] ex i; Norm(i->0, i)
  [Normed   Spec] ex i; Norm(i->0, i)
  
  [Raw Post Spec] Norm(emp, ()); ex f29; Norm(f29->0, f29); Norm(emp, f29)
  [Normed   Post] ex f29; Norm(f29->0, f29)
  
  [Entail  Check] true
  ==========================================
  
  ex f32 i_33 i. T=>T // norm pre
  /\ i_33=0=>0=i_33 // norm post
  /\ i_33+1=1 // norm res eq
  z3: valid
  
  ========== Function: test5_true ==========
  [Specification] ex i; Norm(i->0, 1)
  [Normed   Spec] ex i; Norm(i->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f32; Norm(f32->0, f32); ex i_33; req f32->i_33; Norm(f32->i_33, i_33); Norm(emp, i_33+1)
  [Normed   Post] ex f32 i_33; Norm(f32->i_33 /\ i_33=0, i_33+1)
  
  [Entail  Check] true
  ==========================================
  
  ex f36 i_37 f38 i_39 i. T=>i_37=f38/\i_37+1=i_39 // norm pre
  /\ i_37=0/\f38=i_37/\i_39=i_37+1=>1=i_39 // norm post
  /\ i_39=1 // norm res eq
  z3: valid
  
  ========== Function: test6_true ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f36; Norm(f36->0, f36); ex i_37; req f36->i_37; Norm(f36->i_37, i_37); Norm(emp, i_37+1); ex f38; req f36->f38; Norm(f36->i_37+1, ()); ex i_39; req f36->i_39; Norm(f36->i_39, i_39)
  [Normed   Post] ex f36 i_37 f38 i_39; req i_37=f38/\i_37+1=i_39; Norm(f36->i_39 /\ i_37=0/\f38=i_37/\i_39=i_37+1, i_39)
  
  [Entail  Check] true
  ==========================================
  
  ex res_42. T=>T // norm pre
  /\ T=>T // norm post
  /\ res_42=() // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_42=() // post stage 0
  z3: valid
  
  ========== Function: test11_true ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); Norm(emp, ())
  
  [Raw Post Spec] Norm(emp, ()); ex res_42; Eff(emp, [], res_42); Norm(emp, res_42); Norm(emp, res_42)
  [Normed   Post] ex res_42; Eff(emp, [], res_42); Norm(emp, res_42)
  
  [Entail  Check] true
  ===========================================
  
  ex res_43. T=>T // norm pre
  /\ T=>T // norm post
  /\ 1=() // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_43=() // post stage 0
  z3: not valid
  
  ========== Function: test12_false ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); Norm(emp, ())
  
  [Raw Post Spec] Norm(emp, ()); ex res_43; Eff(emp, [], res_43); Norm(emp, res_43); Norm(emp, 1)
  [Normed   Post] ex res_43; Eff(emp, [], res_43); Norm(emp, 1)
  
  [Entail  Check] false
  ============================================
  
  ex f44 res_45 i_46 f47 i. T=>i_46=z/\i_46=f47 // norm pre
  /\ f47=i_46=>z+1=i_46+1 // norm post
  /\ res_45=ret // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_45=ret/\0=0 // post stage 0
  z3: valid
  
  ========== Function: test_true ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f44; Norm(f44->0, f44); ex res_45; Eff(emp, [], res_45); Norm(emp, res_45); ex i_46; req f44->i_46; Norm(f44->i_46, i_46); Norm(emp, i_46+1); ex f47; req f44->f47; Norm(f44->i_46+1, ()); Norm(emp, res_45)
  [Normed   Post] ex f44 res_45; Eff(f44->0, [], res_45); ex i_46 f47; req f44->i_46 /\ i_46=f47; Norm(f44->i_46+1 /\ f47=i_46, res_45)
  
  [Entail  Check] true
  =========================================
  
  ex f54 res_55 i_56 f57 i_58 i. T=>i_56=z/\i_56=f57/\i_56+1=i_58 // norm pre
  /\ f57=i_56/\i_58=i_56+1=>z+1=i_58 // norm post
  /\ i_58=ret // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_55=ret/\0=0 // post stage 0
  z3: not valid
  
  ========== Function: test1_false ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f54; Norm(f54->0, f54); ex res_55; Eff(emp, [], res_55); Norm(emp, res_55); ex i_56; req f54->i_56; Norm(f54->i_56, i_56); Norm(emp, i_56+1); ex f57; req f54->f57; Norm(f54->i_56+1, ()); ex i_58; req f54->i_58; Norm(f54->i_58, i_58)
  [Normed   Post] ex f54 res_55; Eff(f54->0, [], res_55); ex i_56 f57 i_58; req f54->i_56 /\ i_56=f57/\i_56+1=i_58; Norm(f54->i_58 /\ f57=i_56/\i_58=i_56+1, i_58)
  
  [Entail  Check] false
  ===========================================
  
  
  ========== Function: test2_false ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f65; Norm(f65->0, f65); ex res_66; Eff(emp, [], res_66); Norm(emp, res_66); Norm(emp, res_66)
  [Normed   Post] ex f65 res_66; Eff(f65->0, [], res_66); Norm(emp, res_66)
  
  [Entail  Check] false
  ===========================================
  
  ex f69 res_70 i_71 f72 i. T=>i_71=z/\i_71=f72 // norm pre
  /\ f72=i_71=>z+1=i_71+2 // norm post
  /\ res_70=ret // norm res eq
  /\ T=>T // pre stage 0
  /\ T=>res_70=ret/\0=0 // post stage 0
  z3: not valid
  
  ========== Function: test3_false ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f69; Norm(f69->0, f69); ex res_70; Eff(emp, [], res_70); Norm(emp, res_70); ex i_71; req f69->i_71; Norm(f69->i_71, i_71); Norm(emp, i_71+2); ex f72; req f69->f72; Norm(f69->i_71+2, ()); Norm(emp, res_70)
  [Normed   Post] ex f69 res_70; Eff(f69->0, [], res_70); ex i_71 f72; req f69->i_71 /\ i_71=f72; Norm(f69->i_71+2 /\ f72=i_71, res_70)
  
  [Entail  Check] false
  ===========================================
  
  ex f79 f80 a b. T=>T // norm pre
  /\ T=>0=0 // norm post
  /\ 1=1 // norm res eq
  z3: valid
  
  ========== Function: test13_true ==========
  [Specification] ex a b; Norm(a->0*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->0*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f79; Norm(f79->0, f79); ex f80; Norm(f80->1, f80); Norm(emp, 1)
  [Normed   Post] ex f79 f80; Norm(f79->0*f80->1, 1)
  
  [Entail  Check] true
  ===========================================
  
  ex f83 f84 a b. T=>T // norm pre
  /\ T=>1=0 // norm post
  /\ 1=1 // norm res eq
  z3: not valid
  
  ========== Function: test18_true ==========
  [Specification] ex a b; Norm(a->1*b->0, 1)
  [Normed   Spec] ex a b; Norm(a->1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f83; Norm(f83->0, f83); ex f84; Norm(f84->1, f84); Norm(emp, 1)
  [Normed   Post] ex f83 f84; Norm(f83->0*f84->1, 1)
  
  [Entail  Check] false
  ===========================================
  
  ex f87 f88 a b. T=>T // norm pre
  /\ T=>1=0 // norm post
  /\ 1=1 // norm res eq
  z3: not valid
  
  ========== Function: test14_false ==========
  [Specification] ex a b; Norm(a->1*b->1, 1)
  [Normed   Spec] ex a b; Norm(a->1*b->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f87; Norm(f87->0, f87); ex f88; Norm(f88->1, f88); Norm(emp, 1)
  [Normed   Post] ex f87 f88; Norm(f87->0*f88->1, 1)
  
  [Entail  Check] false
  ============================================
  
  
  ========== Function: test15_true ==========
  [Specification] req a->1; Norm(a->1, 1)
  [Normed   Spec] req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 1)
  [Normed   Post] Norm(emp, 1)
  
  [Entail  Check] false
  ===========================================
  
  ex f91 a. a>0=>T // norm pre
  /\ T=>1=0 // norm post
  /\ 1=1 // norm res eq
  z3: not valid
  
  ========== Function: test16_false ==========
  [Specification] ex a; req a->1; Norm(a->1, 1)
  [Normed   Spec] ex a; req a->1; Norm(a->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f91; Norm(f91->0, f91); Norm(emp, 1)
  [Normed   Post] ex f91; Norm(f91->0, 1)
  
  [Entail  Check] false
  ============================================
  
  
  ========== Function: test17_true ==========
  [Specification] ex b; req a->1; Norm(a->1*b->0, 1)
  [Normed   Spec] ex b; req a->1; Norm(a->1*b->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f94; Norm(f94->0, f94); Norm(emp, 1)
  [Normed   Post] ex f94; Norm(f94->0, 1)
  
  [Entail  Check] false
  ===========================================
  
