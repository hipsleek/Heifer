let f p (*@ ex a; req p->a; Norm(p->a+1, ()) @*) =
  (* {emp |--* req p->a; p->a+1 } *)
  (* {p->a |--* p->a+1 } *)
  let n = !p in
  (* {p->a /\ n=a |--* p->a+1 } *)
  let m = n + 1 in
  (* {p->a /\ n=a /\ m=n+1 |--* p->a+1 } *)
  p := m
(* {p->m /\ n=a /\ m=n+1 |--* p->a+1 } *)
(* {emp} *)
