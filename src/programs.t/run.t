
  $ hip b0_env.ml | ./sanitize.sh
  Effect Foo -> emp
  
  
  ========== Function: goo ==========
  [Pre  Condition] emp
  [Post Condition] emp
  [Final  Effects] Foo.Q(Foo ())
  
  [Verification Result: Fail 
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * Foo.Q(Foo ()) |- emp   [UNFOLD]
  * └── Q(Foo ()) |- _|_   [Bot-RHS]
  
  
  ========== Function: f ==========
  [Pre  Condition] emp
  [Post Condition] emp
  [Final  Effects] emp
  
  [Verification Result: Succeed 
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  
  
  ========== Function: main ==========
  [Pre  Condition] emp
  [Post Condition] emp
  [Final  Effects] emp
  
  [Verification Result: Succeed 
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  

