effect Foo : (unit -> unit)
effect Goo : (unit -> unit)

let pt str = print_string (str)

let effFoo () =
  pt ("Foo\n"); perform Foo

let effGoo () =
  pt ("Goo\n"); perform Goo


let f () 
(*@ requires _^* @*)
(*@ ensures  Foo.Goo.Q(Goo()).Q(Foo()) @*)
  = let a = pt ("Foo\n"); perform Foo in 
    let b = pt ("Goo\n"); perform Goo in 
    b(); a ()

let res1 
  (*@ requires _^* @*)
  (*@ ensures  Foo.Foo @*)
  =
  match f () with
  | _ -> ()
  | effect Foo k ->  pt ("Foo1\n"); 
                     continue k (fun () -> pt ("Foo2\n"); ()); 
                     pt ("Foo3\n")
                     
  | effect Goo k ->  pt ("Goo1\n"); 
                     (continue (Obj.clone_continuation k) (fun () -> pt ("Goo2\n"); ()));  
                     pt ("Goo3\n");
                     continue k (fun () -> pt ("Goo4\n"); ());  
                     pt ("Goo5\n") 



