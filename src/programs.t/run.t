
  $ hip b0_env.ml | ./sanitize.sh
  Effect Foo -> emp
  
  
  ========== Function: foo ==========
  [Pre  Condition] true, emp, 
  [Post Condition] true, emp, 
  [Final  Effects] true/\true, Foo.Q(Foo ()), 
  
  [Verification Result: Fail 
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * Foo.Q(Foo ()) |- emp   [UNFOLD]
  * └── Q(Foo ()) |- _|_   [Bot-RHS]
  
  
  ========== Function: f ==========
  [Pre  Condition] true, emp, 
  [Post Condition] true, emp, 
  [Final  Effects] true/\true/\true, emp, 
  
  [Verification Result: Succeed 
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  
  
  ========== Function: main ==========
  [Pre  Condition] true, emp, 
  [Post Condition] true, emp, 
  [Final  Effects] true/\true, emp, 
  
  [Verification Result: Succeed 
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  

