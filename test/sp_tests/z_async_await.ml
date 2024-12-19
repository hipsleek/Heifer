(* This is the cooperative concurrency library in Multicore OCaml 4.10.0. *)

type 'a status =
  | Done of 'a
  | Waiting of ('a, unit) continuation list

type 'a promise =
  'a status ref

effect Async : (unit -> 'a) -> 'a promise
effect Await : 'a promise -> 'a

let async e = perform (Async e)
let await p = perform (Await p)
let yield() = ignore (async(fun _ -> ()))

let run (main : unit -> unit) : unit =
  let q : (unit -> unit) Queue.t = Queue.create() in
  let next() =
    if not (Queue.is_empty q) then (Queue.take q) () else ()
  in
  let rec fulfill : type a. a promise -> (unit -> a) -> unit = fun p e ->
    match e() with
    | effect (Async e) k ->
        let p = ref (Waiting []) in
        Queue.add (fun () -> continue k p) q;
        fulfill p e
    | effect (Await p) k ->
        begin match !p with
        | Done y ->
            continue k y
        | Waiting ks ->
            p := Waiting (k :: ks);
            next()
        end
    | y ->
        match !p with
        | Waiting ks ->
            List.iter (fun k -> Queue.add (fun () -> continue k y) q) ks;
            p := Done y;
            next()
        | Done _ ->
            assert false
  in
  fulfill (ref (Waiting [])) main


let main () =
  let r = ref None in
  let f() =
    let rec loop() =
      match !r with
      | None   ->
          yield(); loop()
      | Some p ->
          Printf.printf "This line shall be printed...\n";
          await p;
          Printf.printf "...but this line shall never know the world!\n"
    in
    loop ()
  in
  let p = async f in
  r := Some p

let _ =
  run main;
  Printf.printf "[run] has terminated.\n"

let main () =
  let p = async (fun () -> 3) in
  Printf.printf "I have computed %d\n" ((await p) + (await p))

let _ =
  run main
