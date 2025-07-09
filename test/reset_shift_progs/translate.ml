
let hello_lambda ()
(*@ ens res=2 @*)
= (fun x -> x) 2

let hello_string ()
(*@ ens res="a" @*)
= "a"

let hello_string_conc ()
(*@ ens res="a" ++ "b" @*)
= "a" ^ "b"

let undelimited () =
  1 + shift (fun k -> 1)

let hello ()
(*@ ens res=1 @*)
= reset (1 + shift (fun k -> 1))

let hello1 ()
(*@ ens res=2 @*)
= reset (1 + shift (fun k -> (k 1)))

let hello3 ()
(*@ ens res=3 @*)
= let f x = x + x in
  reset (1 + shift (fun k -> (k (f 1))))

let hello41 ()
(*@ ens res=4 @*)
= let f x = x + x in
  (reset (shift (fun k -> (fun x -> k (f x))))) 2

let hello4 ()
(*@ ens res=4 @*)
= (reset (shift (fun k -> (fun x -> k x)))) 4

let hello5 ()
(*@ ens res=5 @*)
= (reset (shift (fun k -> (fun x -> k x)) + 2)) 3

let hello6 ()
(*@ ens res=6 @*)
= ((reset (shift (fun k -> (fun x -> k x)) + shift (fun k -> (fun x -> k x)))) 2) 4

let hello7 ()
(*@ ens res=7 @*)
= ((reset (shift (fun k -> (fun x -> k x)) + shift (fun k -> (fun x -> k x)))) 6) 1

let hello_eta ()
(*@ ens res=2 @*)
= (reset (shift (fun k -> k))) 2

let hello8 ()
(*@ ens res=8 @*)
= ((reset (shift (fun k -> k) + shift (fun k -> k))) 3) 5

let hello_printf ()
(*@ ens res="ab!" @*)
= ((reset (shift (fun k -> k) ^ shift (fun k -> k) ^ "!")) "a") "b"

(*
let hello_shift0 ()
(*@ ens res="A cat has Alice." @*)
= reset ("Alice" ^ reset ("has " ^ shift0 k1 (shift0 k2 ("A cat " ^ k1 (k2 ".")))))
*)

let hello_s2i ()
(*@ ens res="1" @*)
= string_of_int 1

let get_int () =
  shift (fun k -> (fun x -> k (string_of_int x)))

let get_string () =
  shift (fun k -> (fun x -> k x))

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
