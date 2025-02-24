let get_int () =
  shift k (fun x -> k (string_of_int x))

let hello_printf_string1 ()
(*@ ens res="3-2" @*)
= ((reset (let x = get_int () in let y = get_int () in x ^ "-" ^ y)) 3) 2
