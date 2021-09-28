
  $ hip b0_env.ml | ./sanitize.sh
  Effect Foo -> emp
  
  
  ========== Function: foo ==========
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
  

  $ hip state.ml | ./sanitize.sh
  Effect Puts1 -> emp
  Effect Get -> emp
  
  
  
  ========== Function: get ==========
  [Pre  Condition] emp
  [Post Condition] Get
  [Final  Effects] Get
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Get |- Get   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  
  ========== Function: put ==========
  [Pre  Condition] Get
  [Post Condition] Put
  [Final  Effects] Put
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Put |- Put   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  
  ========== Function: f ==========
  [Pre  Condition] emp
  [Post Condition] Get.Put
  [Final  Effects] Get.Put
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Get.Put |- Get.Put   [UNFOLD]
  * └── Put |- Put   [UNFOLD]
  *     └── emp |- emp   [UNFOLD]
  
  
  ========== Function: main ==========
  [Pre  Condition] emp
  [Post Condition] emp
  [Final  Effects] Get.Put
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * Get.Put |- emp   [UNFOLD]
  * └── Put |- _|_   [Bot-RHS]
  
  
