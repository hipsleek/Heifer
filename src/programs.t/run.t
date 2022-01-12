
  $ hip b0_env.ml | ./sanitize.sh
  
  =============== 
  ========== Function: f2 ==========
  [Pre  Condition] (_)^*
  [Post Condition] emp
  [Final  Effects] (Foo).(Q(Foo 5))
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * (Foo).(Q(Foo 5)) |- emp   [UNFOLD]
  * └── Q(Foo 5) |- _|_   [Bot-RHS]
  
  ========== Function: f ==========
  [Pre  Condition] (_)^*
  [Post Condition] emp
  [Final  Effects] emp
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  
  ========== Function: main ==========
  [Pre  Condition] (_)^*
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
  [Final  Effects] (Foo).(Q(Foo ()))
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * (Foo).(Q(Foo ())) |- Foo   [UNFOLD]
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
  
  =============== 
  ========== Function: get ==========
  [Pre  Condition] (_)^*
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
  [Pre  Condition] ((_)^*).(Get)
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
  [Pre  Condition] (_)^*
  [Post Condition] (Get).(Put)
  [Final  Effects] (Get).(Put)
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Get).(Put) |- (Get).(Put)   [UNFOLD]
  * └── Put |- Put   [UNFOLD]
  *     └── emp |- emp   [UNFOLD]
  
  ========== Function: main ==========
  [Pre  Condition] (_)^*
  [Post Condition] emp
  [Final  Effects] (Get).(Put)
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * (Get).(Put) |- emp   [UNFOLD]
  * └── Put |- _|_   [Bot-RHS]
  
  $ hip files.ml | ./sanitize.sh
  
  =============== 
  ========== Function: open_file ==========
  [Pre  Condition] (_)^*
  [Post Condition] Open
  [Final  Effects] Open
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Open |- Open   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  ========== Function: close_file ==========
  [Pre  Condition] ((_)^*).((Open).((!Close)^*))
  [Post Condition] Close
  [Final  Effects] Close
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Close |- Close   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  ========== Function: file ==========
  [Pre  Condition] emp
  [Post Condition] (Open).(Close)
  [Final  Effects] (Open).((Open).(Close))
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * (Open).((Open).(Close)) |- (Open).(Close)   [UNFOLD]
  * └── (Open).(Close) |- Close   [UNFOLD]
  *     └── Close |- _|_   [Bot-RHS]
  
  ========== Function: main ==========
  [Pre  Condition] emp
  [Post Condition] (Open).(Close)
  [Final  Effects] (Open).(Close)
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).(Close) |- (Open).(Close)   [UNFOLD]
  * └── Close |- Close   [UNFOLD]
  *     └── emp |- emp   [UNFOLD]
  
  ========== Function: file1 ==========
  [Pre  Condition] emp
  [Post Condition] (_)^*
  [Final  Effects] (Open).((Open).(Close))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).((Open).(Close)) |- (_)^*   [UNFOLD]
  * └── (Open).(Close) |- (_)^*   [UNFOLD]
  *     └── Close |- (_)^*   [UNFOLD]
  *         └── emp |- (_)^*   [UNFOLD]
  
  ========== Function: file2 ==========
  [Pre  Condition] emp
  [Post Condition] (_)^*
  [Final  Effects] (Open).(Close)
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).(Close) |- (_)^*   [UNFOLD]
  * └── Close |- (_)^*   [UNFOLD]
  *     └── emp |- (_)^*   [UNFOLD]
  
  ========== Function: file3 ==========
  [Pre  Condition] emp
  [Post Condition] (_)^*
  [Final  Effects] (Open).((Open).(Close))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).((Open).(Close)) |- (_)^*   [UNFOLD]
  * └── (Open).(Close) |- (_)^*   [UNFOLD]
  *     └── Close |- (_)^*   [UNFOLD]
  *         └── emp |- (_)^*   [UNFOLD]
  
  ========== Function: file4 ==========
  [Pre  Condition] emp
  [Post Condition] (_)^*
  [Final  Effects] (Open).((Close).((Open).(Close)))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).((Close).((Open).(Close))) |- (_)^*   [UNFOLD]
  * └── (Close).((Open).(Close)) |- (_)^*   [UNFOLD]
  *     └── (Open).(Close) |- (_)^*   [UNFOLD]
  *         └── Close |- (_)^*   [UNFOLD]
  *             └── emp |- (_)^*   [UNFOLD]
  

  $ hip generator.ml | ./sanitize.sh
  
  ========== Function: to_gen ==========
  [Pre  Condition] (_)^*
  [Post Condition] emp
  [Final  Effects] emp
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  
  ========== Function: f ==========
  [Pre  Condition] (_)^*
  [Post Condition] emp
  [Final  Effects] emp
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  
  $ hip flip.ml | ./sanitize.sh
  
  =============== 
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
  [Post Condition] ((Choose).(Choose))+(Choose)
  [Final  Effects] (((Choose).(Choose))+((Choose).(Choose)))+(Choose)
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (((Choose).(Choose))+((Choose).(Choose)))+(Choose) |- ((Choose).(Choose))+(Choose)   [UNFOLD]
  * ├── ((Choose)+(Choose))+(emp) |- (Choose)+(emp)   [UNFOLD]
  * │   ├── (emp)+(emp) |- emp   [UNFOLD]
  * │   └── (emp)+(emp) |- emp   [UNFOLD]
  * ├── ((Choose)+(Choose))+(emp) |- (Choose)+(emp)   [UNFOLD]
  * │   ├── (emp)+(emp) |- emp   [UNFOLD]
  * │   └── (emp)+(emp) |- emp   [UNFOLD]
  * └── ((Choose)+(Choose))+(emp) |- (Choose)+(emp)   [UNFOLD]
  *     ├── (emp)+(emp) |- emp   [UNFOLD]
  *     └── (emp)+(emp) |- emp   [UNFOLD]
  
  ========== Function: all_results ==========
  [Pre  Condition] emp, eff(m) = (_)^* -> A
  [Post Condition] A
  [Final  Effects] A, eff(m) = (_)^* -> A
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * A |- A   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  $ hip transaction.ml | ./sanitize.sh
  
  =============== 
  ========== Function: raise ==========
  [Pre  Condition] (_)^*
  [Post Condition] Exc
  [Final  Effects] Exc
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Exc |- Exc   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  ========== Function: r ==========
  [Pre  Condition] (_)^*
  [Post Condition] emp
  [Final  Effects] emp
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- emp   [UNFOLD]
  
  ========== Function: atomically ==========
  [Pre  Condition] (_)^*, eff(f) = (!Exc)^* -> ((Update)^*).((Exc)+(emp))
  [Post Condition] ((Update)^*).((Exc)+(emp))
  [Final  Effects] ((Update)^*).(Exc), eff(f) = (!Exc)^* -> ((Update)^*).((Exc)+(emp))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * ((Update)^*).(Exc) |- ((Update)^*).((Exc)+(emp))   [UNFOLD]
  * ├── emp |- emp   [UNFOLD]
  * └── ((Update)^*).(Exc) |- ((Update)^*).((Exc)+(emp))   [Reoccur]
  
  ========== Function: := ==========
  [Pre  Condition] (_)^*
  [Post Condition] Update
  [Final  Effects] Update
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Update |- Update   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  ========== Function: error ==========
  [Pre  Condition] (_)^*
  [Post Condition] (Update).((Update).(Exc))
  [Final  Effects] (Update).((Update).(Exc))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Update).((Update).(Exc)) |- (Update).((Update).(Exc))   [UNFOLD]
  * └── (Update).(Exc) |- (Update).(Exc)   [UNFOLD]
  *     └── Exc |- Exc   [UNFOLD]
  *         └── emp |- emp   [UNFOLD]
  
  ========== Function: g ==========
  [Pre  Condition] (_)^*
  [Post Condition] (Update).((Update).(Update))
  [Final  Effects] (Update).((Update).(Update))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Update).((Update).(Update)) |- (Update).((Update).(Update))   [UNFOLD]
  * └── (Update).(Update) |- (Update).(Update)   [UNFOLD]
  *     └── Update |- Update   [UNFOLD]
  *         └── emp |- emp   [UNFOLD]
  
  ========== Function: h ==========
  [Pre  Condition] emp
  [Post Condition] (_)^*
  [Final  Effects] ((Update)^*).((Exc)+(emp))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * ((Update)^*).((Exc)+(emp)) |- (_)^*   [UNFOLD]
  * ├── emp |- (_)^*   [UNFOLD]
  * └── ((Update)^*).((Exc)+(emp)) |- (_)^*   [Reoccur]
  
  $ hip simple_loop.ml | ./sanitize.sh
  
  =============== 
  =============== 
  ========== Function: f ==========
  [Pre  Condition] (_)^*
  [Post Condition] (A)^w
  [Final  Effects] (A).((A)^w)
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (A).((A)^w) |- (A)^w   [UNFOLD]
  * └── (A)^w |- (A)^w   [UNFOLD]
  *     └── (A)^w |- (A)^w   [Reoccur]
  
  ========== Function: g ==========
  [Pre  Condition] (_)^*
  [Post Condition] (A)^*
  [Final  Effects] emp
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * emp |- (A)^*   [UNFOLD]
  
  ========== Function: main ==========
  [Pre  Condition] emp
  [Post Condition] (A)^w
  [Final  Effects] (A)^w
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (A)^w |- (A)^w   [UNFOLD]
  * └── (A)^w |- (A)^w   [Reoccur]
  
