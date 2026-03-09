open Core_lang

let convert_functions_to_staged fns =
  List.map
    (fun (s, d) ->
      match Forward_rules.apply d with
      | Fun b -> (s, b)
      | _ -> failwith "not a function?")
    fns

let get_definitions_and_obligations src =
  let vu = Frontend.parse_ocaml src in
  (* TODO convert pure functions to why3? *)
  (convert_functions_to_staged vu.program_functions, Obligations.generate vu)
