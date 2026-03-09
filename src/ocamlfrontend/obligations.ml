open Core_lang
open Core.Syntax
open Core.Pretty

type t = (term list * term) list

let with_spec_to_subsumption f s =
  let spec = Parsing.Parse.parse_staged_spec s in
  let open Bindlib in
  match Forward_rules.apply f with
  | Fun b ->
      let xs, body = unmbind b in
      Some (Forall (unbox (bind_mvar xs (box_term (Subsumes (body, spec))))))
  | _ -> None

let quantified_entailment_to_named name t =
  let open Bindlib in
  match t with
  | Forall b ->
      let xs, body = unmbind b in
      (match body with
      | Subsumes (_impl, spec) ->
          let xs1 = List.map Tm.var (Array.to_list xs) in
          Some
            (Forall
               (unbox
                  (bind_mvar xs
                     (box_term (Subsumes (Apply (Symbol { sym_name = name }, xs1), spec))))))
      | _ -> None)
  | _ -> None

let rec collect_child_obl t =
  match t with
  | WithSpec (f, s, _name) -> with_spec_to_subsumption f s |> Option.to_list
  | Fun (_, body) | Shift (_, body) | Reset body -> collect_child_obl body
  | Let (_, b1, b2) | Sequence (b1, b2) -> collect_child_obl b1 @ collect_child_obl b2
  | Apply (b1, b2) -> collect_child_obl b1 @ List.concat_map collect_child_obl b2
  | Var _ | Int _ -> []
  | If (_, _, _) | Perform (_, _) | Resume _ | Match (_, _) -> failwith "unsupported for now"

let collect_from_term t =
  match t with
  | WithSpec (f, s, name) ->
      let open Util.Options.Monad in
      let* top_level = with_spec_to_subsumption f s in
      pure (name, top_level, collect_child_obl f)
  | _ -> None

let collect_from_all (ts : (string * expr) list) : t =
  let res, _ =
    List.fold_left
      (fun (res, acc) (_name, t) ->
        (* res is the final result we are build, acc is whatever came before *)
        match collect_from_term t with
        | None ->
            (* if a program function has no spec, it doesn't contribute anything *)
            (* TODO we may want to consider child specs still *)
            (res, acc)
        | Some (name, top, child) ->
            let overall = quantified_entailment_to_named name top |> Option.get in
            (* each thing depends on whatever came before, as well as any child specs, and contributes to the next one *)
            (* TODO when are the child specs proved and what do they depend on? *)
            ((acc @ child, top) :: res, overall :: acc))
      ([], []) ts
  in
  List.rev res

let generate prog = collect_from_all prog.program_functions

let test code =
  let prog = Frontend.parse_ocaml code in
  let obs = generate prog in
  List.iter
    (fun (ass, ob) ->
      Format.printf "@[<v>%a@,-------------@,%a@,@,@]" (Fmt.list ~sep:Fmt.cut pp_term) ass pp_term
        ob)
    obs

(* TODO symbols + *)
let%expect_test "generate proof obligations" =
  let code =
    {|
let [@pure] rec length li =
  match li with
  | [] -> 0
  | x :: xs -> 1 + length xs

let foldr_sum xs k
(*@ sum xs + k @*)
= let g c t = c + t in
  foldr g xs k

let foldr_length xs init
(*@ length xs + init @*)
= let g c t = 1 + t in
  foldr g xs init
|}
  in
  test code;
  [%expect
    {|
    -------------
    forall xs k. (fun c t -> c+t); g. foldr g xs k <: sum xs+k

    forall xs k. foldr_sum xs k <: sum xs+k
    -------------
    forall xs init. (fun c t -> 1+t); g. foldr g xs init <: length xs+init
    |}]

(* TODO tests for child specs *)
