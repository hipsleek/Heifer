open Thread

let n = int_of_float (Sys.time() *. 1000000.0) 

let () = Random.init (n)


let prog1 () =
  let result = ref 0 in
  let f i 
  (*@ requires _^* @*)
  (*@ ensures {v->i} @*)
  =
      print_string ("adding " ^ string_of_int i ^"\n");
      let v = !result in
      let fn = (Random.float 1.0) in 
      (*print_endline ("fn " ^ string_of_float fn);*)
      Thread.delay fn;
      result := v + i;
      print_endline ("Value " ^ string_of_int !result);
  in
  ignore(Thread.create f 1);
  ignore(Thread.create f 2);
  (Thread.create f 3)

let main 
  (*@ requires _^* @*)
  (*@ ensures {v->1} || {v->2} || {v->3}  @*)
= 
  Thread.join (prog1 ()); ()