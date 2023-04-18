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
ex x51; Read(emp, x51); ex r51; Write(emp, (x51+1), r51);
ex x52; Read(emp, x52); ex r52; Write(emp, (x52+1), r52);
ex x53; Read(emp, x53); ex r53; Write(emp, (x53+1), r53);
ex x54; Read(emp, x54); ex r54; Write(emp, (x54+1), r54);
ex x55; Read(emp, x55); ex r55; Write(emp, (x55+1), r55);
ex x56; Read(emp, x56); ex r56; Write(emp, (x56+1), r56);
ex x57; Read(emp, x57); ex r57; Write(emp, (x57+1), r57);
ex x58; Read(emp, x58); ex r58; Write(emp, (x58+1), r58);
ex x59; Read(emp, x59); ex r59; Write(emp, (x59+1), r59);
ex x60; Read(emp, x60); ex r60; Write(emp, (x60+1), r60);
ex x61; Read(emp, x61); ex r61; Write(emp, (x61+1), r61);
ex x62; Read(emp, x62); ex r62; Write(emp, (x62+1), r62);
ex x63; Read(emp, x63); ex r63; Write(emp, (x63+1), r63);
ex x64; Read(emp, x64); ex r64; Write(emp, (x64+1), r64);
ex x65; Read(emp, x65); ex r65; Write(emp, (x65+1), r65);
ex x66; Read(emp, x66); ex r66; Write(emp, (x66+1), r66);
ex x67; Read(emp, x67); ex r67; Write(emp, (x67+1), r67);
ex x68; Read(emp, x68); ex r68; Write(emp, (x68+1), r68);
ex x69; Read(emp, x69); ex r69; Write(emp, (x69+1), r69);
ex x70; Read(emp, x70); ex r70; Write(emp, (x70+1), r70);
ex x71; Read(emp, x71); ex r71; Write(emp, (x71+1), r71);
ex x72; Read(emp, x72); ex r72; Write(emp, (x72+1), r72);
ex x73; Read(emp, x73); ex r73; Write(emp, (x73+1), r73);
ex x74; Read(emp, x74); ex r74; Write(emp, (x74+1), r74);
ex x75; Read(emp, x75); ex r75; Write(emp, (x75+1), r75);
ex x76; Read(emp, x76); ex r76; Write(emp, (x76+1), r76);
ex x77; Read(emp, x77); ex r77; Write(emp, (x77+1), r77);
ex x78; Read(emp, x78); ex r78; Write(emp, (x78+1), r78);
ex x79; Read(emp, x79); ex r79; Write(emp, (x79+1), r79);
ex x80; Read(emp, x80); ex r80; Write(emp, (x80+1), r80);
ex x81; Read(emp, x81); ex r81; Write(emp, (x81+1), r81);
ex x82; Read(emp, x82); ex r82; Write(emp, (x82+1), r82);
ex x83; Read(emp, x83); ex r83; Write(emp, (x83+1), r83);
ex x84; Read(emp, x84); ex r84; Write(emp, (x84+1), r84);
ex x85; Read(emp, x85); ex r85; Write(emp, (x85+1), r85);
ex x86; Read(emp, x86); ex r86; Write(emp, (x86+1), r86);
ex x87; Read(emp, x87); ex r87; Write(emp, (x87+1), r87);
ex x88; Read(emp, x88); ex r88; Write(emp, (x88+1), r88);
ex x89; Read(emp, x89); ex r89; Write(emp, (x89+1), r89);
ex x90; Read(emp, x90); ex r90; Write(emp, (x90+1), r90);
ex x91; Read(emp, x91); ex r91; Write(emp, (x91+1), r91);
ex x92; Read(emp, x92); ex r92; Write(emp, (x92+1), r92);
ex x93; Read(emp, x93); ex r93; Write(emp, (x93+1), r93);
ex x94; Read(emp, x94); ex r94; Write(emp, (x94+1), r94);
ex x95; Read(emp, x95); ex r95; Write(emp, (x95+1), r95);
ex x96; Read(emp, x96); ex r96; Write(emp, (x96+1), r96);
ex x97; Read(emp, x97); ex r97; Write(emp, (x97+1), r97);
ex x98; Read(emp, x98); ex r98; Write(emp, (x98+1), r98);
ex x99; Read(emp, x99); ex r99; Write(emp, (x99+1), r99);
ex x100; Read(emp, x100); ex r100; Write(emp, (x100+1), r100);

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
  Norm(i->100,  100)
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  match test () with
  | v -> !i (*print_string (string_of_int !i) *)
  | effect (Write x) k -> i := x; (continue k ())
  | effect Read k -> (continue k (!i)) 


