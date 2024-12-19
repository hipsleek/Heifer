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
ex x101; Read(emp, x101); ex r101; Write(emp, (x101+1), r101);
ex x102; Read(emp, x102); ex r102; Write(emp, (x102+1), r102);
ex x103; Read(emp, x103); ex r103; Write(emp, (x103+1), r103);
ex x104; Read(emp, x104); ex r104; Write(emp, (x104+1), r104);
ex x105; Read(emp, x105); ex r105; Write(emp, (x105+1), r105);
ex x106; Read(emp, x106); ex r106; Write(emp, (x106+1), r106);
ex x107; Read(emp, x107); ex r107; Write(emp, (x107+1), r107);
ex x108; Read(emp, x108); ex r108; Write(emp, (x108+1), r108);
ex x109; Read(emp, x109); ex r109; Write(emp, (x109+1), r109);
ex x110; Read(emp, x110); ex r110; Write(emp, (x110+1), r110);
ex x111; Read(emp, x111); ex r111; Write(emp, (x111+1), r111);
ex x112; Read(emp, x112); ex r112; Write(emp, (x112+1), r112);
ex x113; Read(emp, x113); ex r113; Write(emp, (x113+1), r113);
ex x114; Read(emp, x114); ex r114; Write(emp, (x114+1), r114);
ex x115; Read(emp, x115); ex r115; Write(emp, (x115+1), r115);
ex x116; Read(emp, x116); ex r116; Write(emp, (x116+1), r116);
ex x117; Read(emp, x117); ex r117; Write(emp, (x117+1), r117);
ex x118; Read(emp, x118); ex r118; Write(emp, (x118+1), r118);
ex x119; Read(emp, x119); ex r119; Write(emp, (x119+1), r119);
ex x120; Read(emp, x120); ex r120; Write(emp, (x120+1), r120);
ex x121; Read(emp, x121); ex r121; Write(emp, (x121+1), r121);
ex x122; Read(emp, x122); ex r122; Write(emp, (x122+1), r122);
ex x123; Read(emp, x123); ex r123; Write(emp, (x123+1), r123);
ex x124; Read(emp, x124); ex r124; Write(emp, (x124+1), r124);
ex x125; Read(emp, x125); ex r125; Write(emp, (x125+1), r125);
ex x126; Read(emp, x126); ex r126; Write(emp, (x126+1), r126);
ex x127; Read(emp, x127); ex r127; Write(emp, (x127+1), r127);
ex x128; Read(emp, x128); ex r128; Write(emp, (x128+1), r128);
ex x129; Read(emp, x129); ex r129; Write(emp, (x129+1), r129);
ex x130; Read(emp, x130); ex r130; Write(emp, (x130+1), r130);
ex x131; Read(emp, x131); ex r131; Write(emp, (x131+1), r131);
ex x132; Read(emp, x132); ex r132; Write(emp, (x132+1), r132);
ex x133; Read(emp, x133); ex r133; Write(emp, (x133+1), r133);
ex x134; Read(emp, x134); ex r134; Write(emp, (x134+1), r134);
ex x135; Read(emp, x135); ex r135; Write(emp, (x135+1), r135);
ex x136; Read(emp, x136); ex r136; Write(emp, (x136+1), r136);
ex x137; Read(emp, x137); ex r137; Write(emp, (x137+1), r137);
ex x138; Read(emp, x138); ex r138; Write(emp, (x138+1), r138);
ex x139; Read(emp, x139); ex r139; Write(emp, (x139+1), r139);
ex x140; Read(emp, x140); ex r140; Write(emp, (x140+1), r140);
ex x141; Read(emp, x141); ex r141; Write(emp, (x141+1), r141);
ex x142; Read(emp, x142); ex r142; Write(emp, (x142+1), r142);
ex x143; Read(emp, x143); ex r143; Write(emp, (x143+1), r143);
ex x144; Read(emp, x144); ex r144; Write(emp, (x144+1), r144);
ex x145; Read(emp, x145); ex r145; Write(emp, (x145+1), r145);
ex x146; Read(emp, x146); ex r146; Write(emp, (x146+1), r146);
ex x147; Read(emp, x147); ex r147; Write(emp, (x147+1), r147);
ex x148; Read(emp, x148); ex r148; Write(emp, (x148+1), r148);
ex x149; Read(emp, x149); ex r149; Write(emp, (x149+1), r149);
ex x150; Read(emp, x150); ex r150; Write(emp, (x150+1), r150);
ex x151; Read(emp, x151); ex r151; Write(emp, (x151+1), r151);
ex x152; Read(emp, x152); ex r152; Write(emp, (x152+1), r152);
ex x153; Read(emp, x153); ex r153; Write(emp, (x153+1), r153);
ex x154; Read(emp, x154); ex r154; Write(emp, (x154+1), r154);
ex x155; Read(emp, x155); ex r155; Write(emp, (x155+1), r155);
ex x156; Read(emp, x156); ex r156; Write(emp, (x156+1), r156);
ex x157; Read(emp, x157); ex r157; Write(emp, (x157+1), r157);
ex x158; Read(emp, x158); ex r158; Write(emp, (x158+1), r158);
ex x159; Read(emp, x159); ex r159; Write(emp, (x159+1), r159);
ex x160; Read(emp, x160); ex r160; Write(emp, (x160+1), r160);
ex x161; Read(emp, x161); ex r161; Write(emp, (x161+1), r161);
ex x162; Read(emp, x162); ex r162; Write(emp, (x162+1), r162);
ex x163; Read(emp, x163); ex r163; Write(emp, (x163+1), r163);
ex x164; Read(emp, x164); ex r164; Write(emp, (x164+1), r164);
ex x165; Read(emp, x165); ex r165; Write(emp, (x165+1), r165);
ex x166; Read(emp, x166); ex r166; Write(emp, (x166+1), r166);
ex x167; Read(emp, x167); ex r167; Write(emp, (x167+1), r167);
ex x168; Read(emp, x168); ex r168; Write(emp, (x168+1), r168);
ex x169; Read(emp, x169); ex r169; Write(emp, (x169+1), r169);
ex x170; Read(emp, x170); ex r170; Write(emp, (x170+1), r170);
ex x171; Read(emp, x171); ex r171; Write(emp, (x171+1), r171);
ex x172; Read(emp, x172); ex r172; Write(emp, (x172+1), r172);
ex x173; Read(emp, x173); ex r173; Write(emp, (x173+1), r173);
ex x174; Read(emp, x174); ex r174; Write(emp, (x174+1), r174);
ex x175; Read(emp, x175); ex r175; Write(emp, (x175+1), r175);
ex x176; Read(emp, x176); ex r176; Write(emp, (x176+1), r176);
ex x177; Read(emp, x177); ex r177; Write(emp, (x177+1), r177);
ex x178; Read(emp, x178); ex r178; Write(emp, (x178+1), r178);
ex x179; Read(emp, x179); ex r179; Write(emp, (x179+1), r179);
ex x180; Read(emp, x180); ex r180; Write(emp, (x180+1), r180);
ex x181; Read(emp, x181); ex r181; Write(emp, (x181+1), r181);
ex x182; Read(emp, x182); ex r182; Write(emp, (x182+1), r182);
ex x183; Read(emp, x183); ex r183; Write(emp, (x183+1), r183);
ex x184; Read(emp, x184); ex r184; Write(emp, (x184+1), r184);
ex x185; Read(emp, x185); ex r185; Write(emp, (x185+1), r185);
ex x186; Read(emp, x186); ex r186; Write(emp, (x186+1), r186);
ex x187; Read(emp, x187); ex r187; Write(emp, (x187+1), r187);
ex x188; Read(emp, x188); ex r188; Write(emp, (x188+1), r188);
ex x189; Read(emp, x189); ex r189; Write(emp, (x189+1), r189);
ex x190; Read(emp, x190); ex r190; Write(emp, (x190+1), r190);
ex x191; Read(emp, x191); ex r191; Write(emp, (x191+1), r191);
ex x192; Read(emp, x192); ex r192; Write(emp, (x192+1), r192);
ex x193; Read(emp, x193); ex r193; Write(emp, (x193+1), r193);
ex x194; Read(emp, x194); ex r194; Write(emp, (x194+1), r194);
ex x195; Read(emp, x195); ex r195; Write(emp, (x195+1), r195);
ex x196; Read(emp, x196); ex r196; Write(emp, (x196+1), r196);
ex x197; Read(emp, x197); ex r197; Write(emp, (x197+1), r197);
ex x198; Read(emp, x198); ex r198; Write(emp, (x198+1), r198);
ex x199; Read(emp, x199); ex r199; Write(emp, (x199+1), r199);
ex x200; Read(emp, x200); ex r200; Write(emp, (x200+1), r200);

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
  Norm(i->200,  200)
@*)
=
  let i = Sys.opaque_identity (ref 0) in 
  match test () with
  | v -> !i (*print_string (string_of_int !i) *)
  | effect (Write x) k -> i := x; (continue k ())
  | effect Read k -> (continue k (!i)) 


