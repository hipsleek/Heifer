
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
  [Post Condition] Put(s)
  [Final  Effects] Put(s)
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Put(s) |- Put(s)   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  ========== Function: f ==========
  [Pre  Condition] (_)^*
  [Post Condition] (Get).(Put(s))
  [Final  Effects] (Get).(Put(s))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Get).(Put(s)) |- (Get).(Put(s))   [UNFOLD]
  * └── Put(s) |- Put(s)   [UNFOLD]
  *     └── emp |- emp   [UNFOLD]
  
  ========== Function: main ==========
  [Pre  Condition] (_)^*
  [Post Condition] emp
  [Final  Effects] (Get).(Put(s))
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * (Get).(Put(s)) |- emp   [UNFOLD]
  * └── Put(s) |- _|_   [Bot-RHS]
  
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
  [Post Condition] Close(s)
  [Final  Effects] Close(s)
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Close(s) |- Close(s)   [UNFOLD]
  * └── emp |- emp   [UNFOLD]
  
  ========== Function: file ==========
  [Pre  Condition] emp
  [Post Condition] (Open).(Close)
  [Final  Effects] (Open).((Open).(Close(fd)))
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * (Open).((Open).(Close(fd))) |- (Open).(Close)   [UNFOLD]
  * └── (Open).(Close(fd)) |- Close   [UNFOLD]
  *     └── Close(fd) |- _|_   [Bot-RHS]
  
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
  [Final  Effects] (Open).((Open).(Close(fd)))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).((Open).(Close(fd))) |- (_)^*   [UNFOLD]
  * └── (Open).(Close(fd)) |- (_)^*   [UNFOLD]
  *     └── Close(fd) |- (_)^*   [UNFOLD]
  *         └── emp |- (_)^*   [UNFOLD]
  
  ========== Function: file2 ==========
  [Pre  Condition] emp
  [Post Condition] (_)^*
  [Final  Effects] (Open).(Close(fd))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).(Close(fd)) |- (_)^*   [UNFOLD]
  * └── Close(fd) |- (_)^*   [UNFOLD]
  *     └── emp |- (_)^*   [UNFOLD]
  
  ========== Function: file3 ==========
  [Pre  Condition] emp
  [Post Condition] (_)^*
  [Final  Effects] (Open).((Open).(Close(fd)))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).((Open).(Close(fd))) |- (_)^*   [UNFOLD]
  * └── (Open).(Close(fd)) |- (_)^*   [UNFOLD]
  *     └── Close(fd) |- (_)^*   [UNFOLD]
  *         └── emp |- (_)^*   [UNFOLD]
  
  ========== Function: file4 ==========
  [Pre  Condition] emp
  [Post Condition] (_)^*
  [Final  Effects] (Open).((Close(fd)).((Open).(Close(fd))))
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * (Open).((Close(fd)).((Open).(Close(fd)))) |- (_)^*   [UNFOLD]
  * └── (Close(fd)).((Open).(Close(fd))) |- (_)^*   [UNFOLD]
  *     └── (Open).(Close(fd)) |- (_)^*   [UNFOLD]
  *         └── Close(fd) |- (_)^*   [UNFOLD]
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
  [Post Condition] Exc(n)
  [Final  Effects] Exc(n)
  
  [Verification Result: Succeed
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Succeed
  * Exc(n) |- Exc(n)   [UNFOLD]
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
  [Final  Effects] (Update).((Update).((Exc(404)).(Update)))
  
  [Verification Result: Fail
  ------------------------------
  [SIDE] Succeed
  - - - - - - - - - - - - - -
  [ENTAILMENT] Fail
  * (Update).((Update).((Exc(404)).(Update))) |- (Update).((Update).(Exc))   [UNFOLD]
  * └── (Update).((Exc(404)).(Update)) |- (Update).(Exc)   [UNFOLD]
  *     └── (Exc(404)).(Update) |- Exc   [UNFOLD]
  *         └── Update |- _|_   [Bot-RHS]
  
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
  
