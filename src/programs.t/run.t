
  $ hip test_new_entail.ml 2>&1 | ./sanitize.sh
  
  ========== Function: test10_t ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  
  
  ========== Function: test6_t ==========
  [Specification] Norm(emp, 0)
  [Normed   Spec] Norm(emp, 0)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] true
  
  
  ========== Function: test7_f ==========
  [Specification] Norm(emp, j)
  [Normed   Spec] Norm(emp, j)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  
  
  ========== Function: test8_f ==========
  [Specification] Norm(emp, k)
  [Normed   Spec] Norm(emp, k)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  
  
  ========== Function: test9_t ==========
  [Specification] ex j; Norm(emp, j)
  [Normed   Spec] ex j; Norm(emp, j)
  
  [Raw Post Spec] Norm(emp, ()); Norm(emp, 0); Norm(emp, 0)
  [Normed   Post] Norm(emp, 0)
  
  [Entail  Check] false
  
  
  ========== Function: test4_t ==========
  [Specification] ex i; Norm(i->0, i)
  [Normed   Spec] ex i; Norm(i->0, i)
  
  [Raw Post Spec] Norm(emp, ()); ex f22; Norm(f22->0, f22); Norm(emp, f22)
  [Normed   Post] ex f22; Norm(f22->0, f22)
  
  [Entail  Check] true
  
  
  ========== Function: test5_t ==========
  [Specification] ex i; Norm(i->0, 1)
  [Normed   Spec] ex i; Norm(i->0, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f23; Norm(f23->0, f23); ex i_24; req f23->i_24; Norm(f23->i_24, i_24); Norm(emp, i_24+1)
  [Normed   Post] ex f23 i_24; Norm(f23->i_24 /\ i_24=0, i_24+1)
  
  [Entail  Check] true
  
  
  ========== Function: test6_t ==========
  [Specification] ex i; Norm(i->1, 1)
  [Normed   Spec] ex i; Norm(i->1, 1)
  
  [Raw Post Spec] Norm(emp, ()); ex f25; Norm(f25->0, f25); ex i_26; req f25->i_26; Norm(f25->i_26, i_26); Norm(emp, i_26+1); ex f27; req f25->f27; Norm(f25->i_26+1, ()); ex i_28; req f25->i_28; Norm(f25->i_28, i_28)
  [Normed   Post] ex f25 i_26 f27 i_28; req i_26=f27/\i_26+1=i_28; Norm(f25->i_28 /\ i_26=0/\f27=i_26/\i_28=i_26+1, i_28)
  
  [Entail  Check] true
  
  
  ========== Function: test11_t ==========
  [Specification] Eff(emp, [], ())
  [Normed   Spec] Eff(emp, [], ()); Norm(emp, ())
  
  [Raw Post Spec] Norm(emp, ()); ex res_29; Eff(emp, [], res_29); Norm(emp, res_29); Norm(emp, res_29)
  [Normed   Post] ex res_29; Eff(emp, [], res_29); Norm(emp, res_29)
  
  [Entail  Check] true
  
  
  ========== Function: test_t ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f30; Norm(f30->0, f30); ex res_31; Eff(emp, [], res_31); Norm(emp, res_31); ex i_32; req f30->i_32; Norm(f30->i_32, i_32); Norm(emp, i_32+1); ex f33; req f30->f33; Norm(f30->i_32+1, ()); Norm(emp, res_31)
  [Normed   Post] ex f30 res_31; Eff(f30->0, [], res_31); ex i_32 f33; req f30->i_32 /\ i_32=f33; Norm(f30->i_32+1 /\ f33=i_32, res_31)
  
  [Entail  Check] true
  
  
  ========== Function: test1_f ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f34; Norm(f34->0, f34); ex res_35; Eff(emp, [], res_35); Norm(emp, res_35); ex i_36; req f34->i_36; Norm(f34->i_36, i_36); Norm(emp, i_36+1); ex f37; req f34->f37; Norm(f34->i_36+1, ()); ex i_38; req f34->i_38; Norm(f34->i_38, i_38)
  [Normed   Post] ex f34 res_35; Eff(f34->0, [], res_35); ex i_36 f37 i_38; req f34->i_36 /\ i_36=f37/\i_36+1=i_38; Norm(f34->i_38 /\ f37=i_36/\i_38=i_36+1, i_38)
  
  [Entail  Check] false
  
  
  ========== Function: test2_f ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f39; Norm(f39->0, f39); ex res_40; Eff(emp, [], res_40); Norm(emp, res_40); Norm(emp, res_40)
  [Normed   Post] ex f39 res_40; Eff(f39->0, [], res_40); Norm(emp, res_40)
  
  [Entail  Check] false
  
  
  ========== Function: test3_f ==========
  [Specification] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  [Normed   Spec] ex i; Eff(i->0, [], ret); req i->z; Norm(i->z+1, ret)
  
  [Raw Post Spec] Norm(emp, ()); ex f41; Norm(f41->0, f41); ex res_42; Eff(emp, [], res_42); Norm(emp, res_42); ex i_43; req f41->i_43; Norm(f41->i_43, i_43); Norm(emp, i_43+2); ex f44; req f41->f44; Norm(f41->i_43+2, ()); Norm(emp, res_42)
  [Normed   Post] ex f41 res_42; Eff(f41->0, [], res_42); ex i_43 f44; req f41->i_43 /\ i_43=f44; Norm(f41->i_43+2 /\ f44=i_43, res_42)
  
  [Entail  Check] false
  

$ hip files_paper.ml | grep Result
