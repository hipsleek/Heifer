type ('a, 'state) state = 'state -> 'a * 'state

let return v env = (v, env)

let bind op f =
    fun env -> 
      let v, env = op env in
      f v env

let (let*) = bind

let get env = env, env

let scope f =
  fun env ->
    let result, _ = f env in
    result, env


let mutate f =
  fun st -> (), f st

let map f st =
  bind st (fun a -> return (f a))

let rec map_list ~f ls =
  match ls with
  | [] -> return []
  | x::xs -> 
      let* x = f x in
      let* xs = map_list ~f xs in
      return (x::xs)

(* monad-aware wrapper around Debug's utilities *)
module Debug = struct
  open Debug

  let span =
    fun show k env ->
      let@ _ = Debug.span show in
      k () env

  let presult_value r = map_presult fst r
  let presult_state r = map_presult snd r

  let (let@) = Debug.(let@)
end
