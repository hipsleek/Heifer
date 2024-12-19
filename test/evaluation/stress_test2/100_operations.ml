effect Read : int 
effect Write : int -> unit 

(* let (i: int ref) = Sys.opaque_identity (ref 0) *)

let read () 
(*@ 
   ex ret; 
   Read(emp, ret);
   Norm(emp, ret)
@*)
= perform Read

let write n 
(*@ 
   ex ret; 
   Write(emp, n,  ret);
   Norm(emp, ret)
@*)
= perform (Write n)



let test ()
(*@ 
ex x1; Read(emp, x1); ex r1; Write(emp, (x1+1), r1);
ex x2; Read(emp, x2); ex r2; Write(emp, (x2+1), r2);
ex x3; Read(emp, x3); ex r3; Write(emp, (x3+1), r3);
ex x4; Read(emp, x4); ex r4; Write(emp, (x4+1), r4);
ex x5; Read(emp, x5); ex r5; Write(emp, (x5+1), r5);
ex x6; Read(emp, x6); ex r6; Write(emp, (x6+1), r6);
ex x7; Read(emp, x7); ex r7; Write(emp, (x7+1), r7);
ex x8; Read(emp, x8); ex r8; Write(emp, (x8+1), r8);
ex x9; Read(emp, x9); ex r9; Write(emp, (x9+1), r9);
ex x10; Read(emp, x10); ex r10; Write(emp, (x10+1), r10);
ex x11; Read(emp, x11); ex r11; Write(emp, (x11+1), r11);
ex x12; Read(emp, x12); ex r12; Write(emp, (x12+1), r12);
ex x13; Read(emp, x13); ex r13; Write(emp, (x13+1), r13);
ex x14; Read(emp, x14); ex r14; Write(emp, (x14+1), r14);
ex x15; Read(emp, x15); ex r15; Write(emp, (x15+1), r15);
ex x16; Read(emp, x16); ex r16; Write(emp, (x16+1), r16);
ex x17; Read(emp, x17); ex r17; Write(emp, (x17+1), r17);
ex x18; Read(emp, x18); ex r18; Write(emp, (x18+1), r18);
ex x19; Read(emp, x19); ex r19; Write(emp, (x19+1), r19);
ex x20; Read(emp, x20); ex r20; Write(emp, (x20+1), r20);
ex x21; Read(emp, x21); ex r21; Write(emp, (x21+1), r21);
ex x22; Read(emp, x22); ex r22; Write(emp, (x22+1), r22);
ex x23; Read(emp, x23); ex r23; Write(emp, (x23+1), r23);
ex x24; Read(emp, x24); ex r24; Write(emp, (x24+1), r24);
ex x25; Read(emp, x25); ex r25; Write(emp, (x25+1), r25);
ex x26; Read(emp, x26); ex r26; Write(emp, (x26+1), r26);
ex x27; Read(emp, x27); ex r27; Write(emp, (x27+1), r27);
ex x28; Read(emp, x28); ex r28; Write(emp, (x28+1), r28);
ex x29; Read(emp, x29); ex r29; Write(emp, (x29+1), r29);
ex x30; Read(emp, x30); ex r30; Write(emp, (x30+1), r30);
ex x31; Read(emp, x31); ex r31; Write(emp, (x31+1), r31);
ex x32; Read(emp, x32); ex r32; Write(emp, (x32+1), r32);
ex x33; Read(emp, x33); ex r33; Write(emp, (x33+1), r33);
ex x34; Read(emp, x34); ex r34; Write(emp, (x34+1), r34);
ex x35; Read(emp, x35); ex r35; Write(emp, (x35+1), r35);
ex x36; Read(emp, x36); ex r36; Write(emp, (x36+1), r36);
ex x37; Read(emp, x37); ex r37; Write(emp, (x37+1), r37);
ex x38; Read(emp, x38); ex r38; Write(emp, (x38+1), r38);
ex x39; Read(emp, x39); ex r39; Write(emp, (x39+1), r39);
ex x40; Read(emp, x40); ex r40; Write(emp, (x40+1), r40);
ex x41; Read(emp, x41); ex r41; Write(emp, (x41+1), r41);
ex x42; Read(emp, x42); ex r42; Write(emp, (x42+1), r42);
ex x43; Read(emp, x43); ex r43; Write(emp, (x43+1), r43);
ex x44; Read(emp, x44); ex r44; Write(emp, (x44+1), r44);
ex x45; Read(emp, x45); ex r45; Write(emp, (x45+1), r45);
ex x46; Read(emp, x46); ex r46; Write(emp, (x46+1), r46);
ex x47; Read(emp, x47); ex r47; Write(emp, (x47+1), r47);
ex x48; Read(emp, x48); ex r48; Write(emp, (x48+1), r48);
ex x49; Read(emp, x49); ex r49; Write(emp, (x49+1), r49);
ex x50; Read(emp, x50); ex r50; Write(emp, (x50+1), r50);


  ex x3000; 
  Read(emp, x3000); 
  Norm(emp, x3000)
@*)
= 
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  write(read () + 1);
  read () 




let write_handler  ()
(*@ 
  ex i; 
  Norm(i->50,  50)
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  match test () with
  | v -> !i (*print_string (string_of_int !i) *)
  | effect (Write x) k -> i := x; (continue k ())
  | effect Read k -> (continue k (!i)) 


