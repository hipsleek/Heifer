
let incr x = x := !x + 1

let ignore _ = ()

let main h
= let r = ref 0 in
  let awkward = fun f (*@ ex r r1; ens r->0; incr(r, r1); ex r2; h((), r2); ex r3; incr(r, r3) @*) ->
    assert (!r = 0);
    incr r;
    f();
    incr r
  in
  ignore (awkward (fun () -> ignore (awkward (fun () -> ()))))
