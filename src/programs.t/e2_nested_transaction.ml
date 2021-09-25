
type bottom

module type TXN = sig
  type 'a t
  val atomically : (unit -> unit) -> unit
  val ref : 'a -> 'a t
  val (!) : 'a t -> 'a
  val (:=) : 'a t -> 'a -> unit
end

module Txn : TXN = struct
  type 'a t = 'a ref

  effect Update : 'a t * 'a -> unit

  let atomically f =
  (* requires emp /\ Eff(f()) = U^*.(Res \/ emp)
     ensures  U^*.(Res \/ emp) *)


    let comp =
      match f () with
      | x -> (fun _ -> x)
      | exception e -> (fun rb -> rb (); raise e)
      | effect (Update (r,v)) k -> (fun rb ->
          let old_v = !r in
          r := v;
          continue k () (fun () -> r := old_v; rb ()))
    in comp (fun () -> ())

  let ref = ref
  let (!) = (!)
  let (:=) r v
(* requires emp
   ensures  Update.Q(Update(r,v)) *)
  = perform (Update (r,v))
end

open Txn

let account1 = ref 10
let account2 = ref 0

let banking_charges () =
  atomically (fun () ->
    Format.printf "deducting banking charges... @?";
    account1 := !account1 - 1;

    if !account1 < 0 then
      failwith "insufficient balance!"
    else
      print_endline "ok!")

let transfer n =
  atomically (fun () ->
    banking_charges ();

    Format.printf "attempting to transfer %d... @?" n;
    account1 := !account1 - n;
    account2 := !account2 + n;

    if !account1 < 0 then
      failwith "insufficient balance!"
    else
      print_endline "ok!")

let print_balance () =
  Format.printf "account1: %d\naccount2: %d@." !account1 !account2

let move_money () =
  print_balance ();
  begin try
    transfer 9;
    transfer 4;
  with Failure s ->
    print_endline s
  end;
  print_balance ()

let () =
  move_money ()
