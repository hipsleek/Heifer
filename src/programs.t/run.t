
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
  

  $ hip b1_env.ml | ./sanitize.sh
  
  
  ========== Function: main ==========
  [Pre  Condition] emp
  [Post Condition] Foo
  [Final  Effects] Foo.Q(Foo ())
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * Foo.Q(Foo ()) |- Foo   [UNFOLD]
  * └── Q(Foo ()) |- emp   [UNFOLD]
  *     └── emp |- _|_   [DISPROVE]
  

  $ hip b2_open.ml | ./sanitize.sh
  
  --- Module A---
  
  ========== Function: f ==========
  [Pre  Condition] emp
  [Post Condition] Foo
  [Final  Effects] Foo
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Foo |- Foo   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  
  
  ========== Function: main ==========
  [Pre  Condition] emp
  [Post Condition] Foo
  [Final  Effects] Foo
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Foo |- Foo   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  

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
  
  
  $ hip generator.ml | ./sanitize.sh
  
  
  ========== Function: to_gen ==========
  [Pre  Condition] emp
  [Post Condition] emp
  [Final  Effects] emp
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  
  
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
  
  
  $ hip flip.ml | ./sanitize.sh
  Effect Choose -> emp
  
  
  ========== Function: choose ==========
  [Pre  Condition] (_)^*
  [Post Condition] Choose
  [Final  Effects] Choose
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Choose |- Choose   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  
  ========== Function: toss ==========
  [Pre  Condition] (_)^*
  [Post Condition] Choose.Choose+Choose
  [Final  Effects] Choose.Choose+Choose.Choose+Choose
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Choose.Choose+Choose.Choose+Choose |- Choose.Choose+Choose   [UNFOLD]
  * ├── Choose+Choose+emp |- Choose+emp   [UNFOLD]
  * │   ├── emp+emp |- emp   [UNFOLD]
  * │   └── emp+emp |- emp   [UNFOLD]
  * ├── Choose+Choose+emp |- Choose+emp   [UNFOLD]
  * │   ├── emp+emp |- emp   [UNFOLD]
  * │   └── emp+emp |- emp   [UNFOLD]
  * └── Choose+Choose+emp |- Choose+emp   [UNFOLD]
  *     ├── emp+emp |- emp   [UNFOLD]
  *     └── emp+emp |- emp   [UNFOLD]
  
  
  ========== Function: all_results ==========
  [Pre  Condition] emp
  [Post Condition] emp
  [Final  Effects] emp
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  
  
