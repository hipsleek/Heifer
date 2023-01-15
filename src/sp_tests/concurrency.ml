open Thread

let prog1 n =
  let result = ref 0 in
  let f i =
    for j = 0 to n do
      let v = !result in
      (*plet fn = (Random.float 1.0) in 
      rint_endline ("fn " ^ string_of_float fn);
      Thread.delay fn;*)
      result := v + i;
      print_endline ("Value " ^ string_of_int !result);
      flush stdout
    done
  in
  ignore (Thread.create f 1);
  (Thread.create f 2)

let main = Thread.join (prog1 3); ()