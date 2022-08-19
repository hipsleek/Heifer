
  $ hip b0_env.ml | ./sanitize.sh
  
  ========== Function: f2 ==========
  [Pre  Condition] (true, (_)^*, ())
  [Post Condition] (true, emp, ())
  [Final  Effects] (true/\true/\true, (_)^*.(Foo!), ())
  
  
  ========== Function: f ==========
  [Pre  Condition] (true, (_)^*, ())
  [Post Condition] (true, emp, ())
  [Final  Effects] (true/\true, (_)^*, ())
  
  
  ========== Function: main ==========
  [Pre  Condition] (true, (_)^*, ())
  [Post Condition] (true, emp, ())
  [Final  Effects] (true/\true/\true, (_)^*, ())
  
  
  nan out of 0
  11.8763333333 out of 3
  

  $ hip b1_env.ml | ./sanitize.sh
  Fatal error: exception Stdlib.Parsing.Parse_error
  [1]

  $ hip b2_open.ml | ./sanitize.sh
  Fatal error: exception Stdlib.Parsing.Parse_error
  [1]

  $ hip state.ml | ./sanitize.sh
  Fatal error: exception Stdlib.Parsing.Parse_error
  [1]
  $ hip files.ml | ./sanitize.sh
  Fatal error: exception Stdlib.Parsing.Parse_error
  [1]

  $ hip generator.ml | ./sanitize.sh
  
  ========== Function: to_gen ==========
  [Pre  Condition] (true, (_)^*, ())
  [Post Condition] (true, emp, ())
  [Final  Effects] (true/\true, (_)^*, ())
  
  
  ========== Function: f ==========
  [Pre  Condition] (true, (_)^*, ())
  [Post Condition] (true, emp, ())
  [Final  Effects] (true/\true, (_)^*, ())
  
  
  nan out of 0
  9.631 out of 2
  
  $ hip flip.ml | ./sanitize.sh
  Fatal error: exception Stdlib.Parsing.Parse_error
  [1]
  $ hip transaction.ml | ./sanitize.sh
  Fatal error: exception Stdlib.Parsing.Parse_error
  [1]
  $ hip simple_loop.ml | ./sanitize.sh
  Fatal error: exception Stdlib.Parsing.Parse_error
  [1]
