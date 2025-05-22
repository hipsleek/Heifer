let parse_disj_effect_spec = Parser.only_disj_effect_spec
let tokenizer = Lexer.token
let lexbuf_of_string = Lexing.from_string

let parse_disj_effect_spec spec = parse_disj_effect_spec tokenizer (lexbuf_of_string spec)

open Ocaml_compiler

let parse_spec_attribute attr =
  let spec_attribute_name = "spec" in
  let open Ocaml_common.Parsetree in
  (* TODO use ppxlib to do this matching instead; it would be a lot cleaner... *)
  match attr with
  | { attr_name = {txt = attr_name; _};
      attr_payload = PStr [{pstr_desc = Pstr_eval ({pexp_desc = Pexp_constant {pconst_desc = Pconst_string (annotation, _, _); _}}, _)}];
      _} when String.equal attr_name spec_attribute_name -> Some (parse_disj_effect_spec annotation)
  | _ -> None

(** Given a list of Parsetree attributes, return the first found
    attribute corresponding to a specification. *)
let extract_spec_attribute attrs =
  match List.filter_map parse_spec_attribute attrs with
  | spec::_ -> Some spec
  | _ -> None
