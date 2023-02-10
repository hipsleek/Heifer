effect Twice : int
effect Once : int
effect Zero : int
effect Done : unit

let callee0 () : int
(*@  requires (true, emp)   @*)
(*@  ensures  (true, {i->0}.Zero.{i->i+1}.[i=1], ret = ()) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  let ret = perform Zero in 
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1);
  ret


let callee1 () : int
(*@  requires (true, emp)   @*)
(*@  ensures  (true, {i->0}.Once.{i->i+1}.[i=1], ret = ()) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  let ret = perform Once in 
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1);
  ret

(* 1. ASSERTION IN THE SPEC *)
(* 2. MUILTISHOT GENERALISE *)

let callee2 () : int
(*@  requires (true, emp)   @*)
(*@  ensures  (true, {i->0}.Twice.{i->i+1}.[i=1], ret = ()) @*)
= 
  let i = Sys.opaque_identity (ref 0) in
  let ret = perform Twice in
  i := !i + 1;
  Printf.printf "i = %d\n%!" !i;
  assert (!i = 1);
  ret


let main_aux (): int
(*@  requires (true, emp) @*)
(*@  ensures  (true,  {i->0}.{i->i+1}.[i=1].Done.{i->i+1}.[i=1].Done) @*)
=
  match callee0 () with
  | v -> v
  | effect Zero k -> 0 
(*      
For Zero:                                                          
{i->0}.Zero.{i:=old(i)+1}.[i=1]   (Zero(i:=old(i)+1).[i=1])
    currenct effects       continuation k                    heap /\ assertion 
    --------------------------------------------------------------------------------
    {i->0}                 Zero.{i:=old(i)+1}.[i=1]          i=0 
    Zero                   emp                               i=0 (no assertions) 
*)
  | effect Once k ->
    (continue k 1); 
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
    let _ = (continue (Obj.clone_continuation k) 1) in  (continue k 2)
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


let main_aux1 (): int
(*@  requires (true, emp) @*)
(*@  ensures  (true,  {i->0}.{i->i+1}.[i=1].Done.{i->i+1}.[i=1].Done) @*)
=
  match callee0 () with
  | v -> print_string (string_of_int v) ; v
  | effect Zero k -> -1

let main = 
  let a  = main_aux1 () in 
  print_string (string_of_int a)
