let hello_printf ()
(*@ ens res="ab!" @*)
= ((reset (shift k k ^ shift k k ^ "!")) "a") "b"

let hello_shift0 ()
(*@ ens res="A cat has Alice." @*)
= reset ("Alice" ^ reset ("has " ^ shift0 k1 (shift0 k2 ("A cat " ^ k1 (k2 ".")))))

let get_int () =
  shift k (fun x -> k (string_of_int x))

let get_string () =
  shift k (fun x -> k x)

let hello_printf_int ()
(*@ ens res="3!" @*)
= (reset (get_int () ^ "!")) 3


let hello_printf_string1 ()
(*@ ens res="3-2" @*)
= ((reset (let x = get_int () in let y = get_int () in x ^ "-" ^ y)) 3) 2

let hello_printf ()
(*@ ens res="3 hi" @*)
= ((reset (get_int () ^ " " ^ get_string ())) 3) "hi"

let hello_printf_false ()
(*@ ens res="3 hi!" @*)
= ((reset (get_int () ^ " " ^ get_string ())) 3) "hi"
