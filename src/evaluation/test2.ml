effect Eff : unit 

let test ()  
(*@ ex r1 r2 r3 r4 r5 r6 r7 r8 r9;
   Eff(emp, r1);
   Eff(emp, r2);
   Eff(emp, r3);
   Eff(emp, r4);
      Eff(emp, r5);
        Eff(emp, r6);
          Eff(emp, r7);
          Eff(emp, r8);
          Eff(emp, r9);
  Norm(emp, r9)

@*)
= 
  perform Eff;
  perform Eff;
  perform Eff



let main_aux ()
(*@ ex i;
   Norm(i->4, 4)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  (match test () with
  | v -> v 
  | effect Eff k ->
    i:=!i+1;
    i:=!i+1;
    i:=!i+1;
    (continue (Obj.clone_continuation k) ())
  );


