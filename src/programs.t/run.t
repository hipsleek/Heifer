
  $ hip files_paper.ml | ./sanitize.sh
  
  ========== Function: open_file ==========
  [Pre  Condition] (true, (_)^*, ())
  [Post Condition] (true, (Open n)!, ())
  [Final  Effects] (true, (_)^*.(Open n)!, ())
  ~~~~~~~~~~~~~~~~~~~~~
  [TRS Result: Succeed
  - - - - - - - - - - - - - -
  * (_)^*.(Open n)! |- (_)^*.(Open n)!   [UNFOLD]
  * ├── ((_)^*.(Open n)!)+(emp) |- ((_)^*.(Open n)!)+(emp)
  * │   ├── (_)^*.(Open n)! |- (_)^*.(Open n)!   [Reoccur]
  * │   └── emp |- ((_)^*.(Open n)!)+(emp)
  * │       ├── emp |- (_)^*.(Open n)!   [DISPROVE]
  * │       └── emp |- emp   [UNFOLD]
  * └── (_)^*.(Open n)! |- (_)^*.(Open n)!   [Reoccur]
  
  
  ========== Function: close_file ==========
  [Pre  Condition] (true, (_)^*.(Open n)!.(~(Close n)!)^*, ())
  [Post Condition] (true, (Close n)!, ())
  [Final  Effects] (true, (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!, ())
  ~~~~~~~~~~~~~~~~~~~~~
  [TRS Result: Succeed
  - - - - - - - - - - - - - -
  * (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)! |- (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!   [UNFOLD]
  * ├── ((_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!)+(emp.(~(Close n)!)^*.(Close n)!) |- ((_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!)+(emp.(~(Close n)!)^*.(Close n)!)
  * │   ├── (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)! |- (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!   [Reoccur]
  * │   └── (~(Close n)!)^*.(Close n)! |- ((_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!)+((~(Close n)!)^*.(Close n)!)
  * │       ├── (~(Close n)!)^*.(Close n)! |- (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!   [UNFOLD]
  * │       │   ├── emp |- (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!   [DISPROVE]
  * │       │   └── _|_ |- (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!   [Bot-LHS]
  * │       └── (~(Close n)!)^*.(Close n)! |- (~(Close n)!)^*.(Close n)!   [UNFOLD]
  * │           ├── emp |- emp   [UNFOLD]
  * │           └── _|_ |- _|_   [Bot-LHS]
  * └── (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)! |- (_)^*.(Open n)!.(~(Close n)!)^*.(Close n)!   [Reoccur]
  
  
  ========== Function: file_9 ==========
  [Pre  Condition] (true, emp, ())
  [Post Condition] (true, (Open 9)!.(Open 8)!.(Close 9)!, ())
  [Final  Effects] (true, (Open 9)!.(Open 8)!.(Close 9)!, ())
  ~~~~~~~~~~~~~~~~~~~~~
  [TRS Result: Succeed
  - - - - - - - - - - - - - -
  * (Open 9)!.(Open 8)!.(Close 9)! |- (Open 9)!.(Open 8)!.(Close 9)!   [UNFOLD]
  * └── (Open 8)!.(Close 9)! |- (Open 8)!.(Close 9)!   [UNFOLD]
  *     └── (Close 9)! |- (Close 9)!   [UNFOLD]
  *         └── emp |- emp   [UNFOLD]
  
  
  ========== Function: main ==========
  [Pre  Condition] (true, emp, ())
  [Post Condition] (true, Open(9).(_)^*.Close(9), ())
  [Final  Effects] (true, Open(9).Open(8).Close(9), ())
  ~~~~~~~~~~~~~~~~~~~~~
  [TRS Result: Succeed
  - - - - - - - - - - - - - -
  * Open(9).Open(8).Close(9) |- Open(9).(_)^*.Close(9)   [UNFOLD]
  * └── Open(8).Close(9) |- (_)^*.Close(9)   [UNFOLD]
  *     └── Close(9) |- (_)^*.Close(9)   [UNFOLD]
  *         └── emp |- ((_)^*.Close(9))+(emp)
  *             ├── emp |- (_)^*.Close(9)   [DISPROVE]
  *             └── emp |- emp   [UNFOLD]
  
  
  
  $ hip files_paper.ml | grep Result
  [TRS Result: Succeed
  [TRS Result: Succeed
  [TRS Result: Succeed
  [TRS Result: Succeed
