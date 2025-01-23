let get () =
  shift k (fun state -> k state state)

let tick () =
  shift k (fun state -> k () (state + 1))

let run_state thunk =
  (reset (let result = thunk () in fun state -> result)) 0

let main ()
(*@ ens res = 1 @*)
= run_state (fun () ->
    tick ();
    tick ();
    let a = get () in
    tick ();
    get () - a)

let main1 ()
(*@ ens res = 1 @*)
= run_state (fun () -> tick (); get())
