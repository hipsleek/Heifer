let get_int () =
  shift k (fun x -> k (string_of_int x))

let hello_printf_int ()
  (*@ ens res="3!" @*)
= (reset (get_int () ^ "!")) 3
