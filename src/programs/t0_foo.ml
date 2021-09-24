effect Foo : (unit -> unit)


let f g
(*@ requires eff(g) = emp, true, emp @*)
(*@ ensures  Foo @*)
= perform Foo

let h n
(*@ requires Foo.Q(Foo 1) @*)
(*@ ensures  Foo @*)
= perform Foo ()

let h n
(*@ requires emp, 1 + (2-1) < 1 @*)
(*@ ensures  emp @*)
= perform Foo ()



let res_f
  (*@ requires emp @*)
  (*@ ensures Foo  @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->
     continue k (fun () -> ())

     (*
f :: int -> int -> int 
es_f_pre, es_f_post

g :: int -> int 
es_g_pre, es_g_post

e1 = f 1 

e2 = g 1

e1 e2 = f 1 (g 1)

1 : _*, emp 
x : _*, emp 
f 1 : es_f_pre, es_f_post

E (lookup(e1)) = es_f_pre, es_f_post
E (lookup(e2)) = es_g_pre, es_g_post
*)