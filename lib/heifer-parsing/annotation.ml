
open Parsing

let parse_staged_spec spec = Parser.parse_staged_spec Lexer.token (Lexing.from_string spec)

let parse_spec_attribute (attr : Parsetree.attribute) : Hipcore.Hiptypes.staged_spec option =
  let spec_attribute_name = "spec" in
  let open Ocaml_compiler.Ocaml_common.Parsetree in
  (* TODO use ppxlib to do this matching instead; it would be a lot cleaner... *)
  match attr with
  | { attr_name = {txt = attr_name; _};
      attr_payload = PStr [{
        pstr_desc = Pstr_eval ({
          pexp_desc = Pexp_constant {
            pconst_desc = Pconst_string (annotation, _, _); _}; _}, _); _}]; _} ->
      print_string attr_name;
      (* when String.equal attr_name spec_attribute_name -> *)
      if String.equal attr_name spec_attribute_name
      then Some (parse_staged_spec annotation)
      else None
  | _ ->
      None

let extract_attribute parser attrs =
  match List.filter_map parser attrs with
  | item :: _ -> Some item
  | _ -> None

let extract_spec_attribute attrs = extract_attribute parse_spec_attribute attrs
