let get ()
= shift k (fun state -> (k state) state)

(* the version below does not work,
   because our translation does not
   express curried application *)
let get' ()
= shift k (fun state -> k state state)

let tick ()
= shift k (fun state -> (k ()) (state + 1))

let run_state thunk
= (reset (let result = thunk () in fun state -> result)) 0

let main_body ()
= tick ();
  tick ();
  let a = get () in
  tick ();
  get () - a

let main ()
(*@ ens res = 1 @*)
= run_state main_body

let main1_body ()
= tick(); get()

let main1 ()
(*@ ens res = 1 @*)
= run_state main1_body

let main2_body ()
= 2

let main2 ()
(*@ ens res = 2 @*)
= run_state main2_body
