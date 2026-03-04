
(* Section 3.3 in Modular Specification and Verification of Closures in Rust *)
let roll_dice () (*@ ens res>0 @*) = 4 (* FIXME: Should be random *)
let call_ret f
(*@ req f <: (fun v r (*@ req v>0; ens r>0 @*)) @*)
= let x = roll_dice () in f x

let closure_with_hof_false ()
(*@ ens T @*)
= let x = ref (-1) in
  let cl i = let r = !x in x := !x + i; r in
  (* x is still -1 *)
  call_ret cl

let closure_with_hof_ok ()
= let x = ref (-1) in
  let cl i = let r = !x in x := !x + i; r in
  cl 2; (* x is now 1 *)
  call_ret cl