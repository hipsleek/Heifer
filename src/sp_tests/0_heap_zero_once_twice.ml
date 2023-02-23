effect Twice : unit
effect Once : unit
effect Zero : unit
effect Done : unit

let callee0 () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, {i->0}.Zero.{i->i+1}.[i=1], ()) @*)
(*  ensures  (true, # {i->0}; 
                        Zero requires true   
                             ensures {i->i+1}.[i=1]; () ) *)
(*  ensures  (true, # {emp}; ret 1 ) *)
= 
  let i = Sys.opaque_identity (ref 0) in 
  perform Zero;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)


let callee1 () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, {i->0}.Once.{i->i+1}.[i=1], ()) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Once;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

(* 1. ASSERTION IN THE SPEC *)
(* 2. MUILTISHOT GENERALISE *)

let callee2 () 
(*@  requires (true, emp, ())   @*)
(*@  ensures  (true, {i->0}.Twice.{i->i+1}.[i=1], ()) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  perform Twice;
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1)

let main_aux ()
(*@  requires (true, emp, ()) @*)
(*@  ensures  (true,  {i->0}, ()) @*)
=
  match callee1 () with
  | v -> print_string ("Done 0 \n"); perform Done 
  | effect Zero k -> ()
(*      
For Zero:                                                          
{i->0}.Zero.{i:=old(i)+1}.[i=1]   (Zero(i:=old(i)+1).[i=1])
    currenct effects       continuation k                    heap /\ assertion 
    --------------------------------------------------------------------------------
    {i->0}                 Zero.{i:=old(i)+1}.[i=1]          i=0 
    Zero                   emp                               i=0 (no assertions) 
*)
  | effect Once k ->
    (continue k ()); 
(*      
For Once: 
{i->0}.Once.{i:=old(i)+1}.[i=1]   (Once(i:=old(i)+1).[i=1])
    currenct effects       continuation k                      heap /\ assertion  
    --------------------------------------------------------------------------------
    {i->0}                 Once.{i:=old(i)+1}.[i=1]            i=0  
    Once                   {i:=old(i)+1}.[i=1]                 i=0 
    {i:=old(i)+1}          [i=1]                               i=1 
    [i=1]                  emp                                 i=1 /\ true 
*)
  | effect Twice k ->
    (continue (Obj.clone_continuation k) ()); (continue k ())
(*      
For TWICE: 
{i->0}.Twice.{i:=old(i)+1}.[i=1] 
     currenct effects      continuation k                             heap /\ assertion        
    --------------------------------------------------------------------------------
     {i->0}                Twice.{i:=old(i)+1}.[i=1]                  i=0 
     TWICE                 {i:=old(i)+1}.[i=1].{i:=old(i)+1}.[i=1]    i=0 
     {i:=old(i)+1}         [i=1].{i:=old(i)+1}.[i=1]                  i=1
     [i=1]                 {i:=old(i)+1}.[i=1]                        i=1 /\ true 
     {i:=old(i)+1}         [i=1]                                      i=2 
     [i=1]                 emp                                        i=2 /\ false 
*)


let main 
(*@  requires (true, emp, ()) @*)
(*@  ensures  (true, emp, ()) @*)
= 
  match main_aux () with 
  | x ->  ()
  | effect Done k -> print_string ("Done here\n"); continue k ()
