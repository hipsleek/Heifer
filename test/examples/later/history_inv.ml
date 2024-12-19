(* Section 3.2 in Modular Specification and Verification of Closures in Rust *)
let closure_with_history_invariant i j
(*@ ex iv jv; req i->iv*j->jv; ens i->1*j->2 @*)
= let count = ref 0 in
  let cl ()
  (*@ ex a; req count->a; ens count->a+1/\res=a+1 @*)
  = count := !count + 1;
    !count in
  i := cl();
  j := cl()