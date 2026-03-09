open Util.Strings
open Prover.Interactive.State
open Prover

let read_file filename =
  let ic = open_in filename in
  let s = In_channel.input_all ic in
  close_in ic;
  let sdefns, obs = Ocamlfrontend.get_definitions_and_obligations s in
  List.iter (fun (s, d) -> declare_defn { sym_name = s } d) sdefns;
  let new_goals =
    List.map
      (fun (ass, ob) ->
        let assumptions = List.mapi (fun i a -> (Format.asprintf "H%d" i, a)) ass |> SMap.of_list in
        Pctx.create ~assumptions ob)
      obs
  in
  add_goals new_goals;
  set_mode Mode_goal;
  print_proof_state ()
