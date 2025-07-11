
open Parsing

let handle_error parser lexbuf =
  try parser Lexer.token lexbuf with
    | Lexer.Lexing_error msg ->
      Printf.eprintf "Lexing error: %s\n" msg;
      failwith "lexer error"
    | Parser.Error ->
      let pos = Lexing.lexeme_start_p lexbuf in
      let line = pos.Lexing.pos_lnum in
      let column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
      let token = Lexing.lexeme lexbuf in
      Printf.eprintf
        "Parse error at line %d, column %d: unexpected token '%s'\n" line column
        token;
      failwith "parse error"

let parse_staged_spec spec =
  handle_error Parser.parse_staged_spec (Lexing.from_string spec)

let parse_pi spec =
  handle_error Parser.parse_pi (Lexing.from_string spec)

let parse_lemma spec =
  handle_error Parser.parse_lemma (Lexing.from_string spec)

let parse_kappa spec = Parser.parse_kappa Lexer.token (Lexing.from_string spec)

let parse_term spec = Parser.parse_term Lexer.token (Lexing.from_string spec)

let parse_state spec = Parser.parse_state Lexer.token (Lexing.from_string spec)

let string_of_payload (p : Parsetree.payload) =
  match p with
  | PStr [{
      pstr_desc = Pstr_eval ({
        pexp_desc = Pexp_constant {
          pconst_desc = Pconst_string (annotation, _, _); _}; _}, _); _}] -> 
            Some annotation
  | _ -> None

let attribute_parser (attr_name : string) (payload_parser : Parsetree.payload -> 'a option) attr =
  let open Ocaml_compiler.Ocaml_common.Parsetree in
  (* TODO use ppxlib to do this matching instead; it would be a lot cleaner... *)
  if String.equal attr.attr_name.txt attr_name
  then payload_parser attr.attr_payload
  else None

let parse_spec_attribute = attribute_parser "spec" (fun p -> Option.map parse_staged_spec (string_of_payload p))
let parse_ignore_attribute = attribute_parser "ignore" (fun _ -> Some ())
let parse_lemma_attribute = attribute_parser "lemma" (fun p -> Option.map parse_lemma (string_of_payload p))

let extract_attribute parser attrs =
  match List.filter_map parser attrs with
  | item :: _ -> Some item
  | _ -> None

let extract_spec_attribute attrs = extract_attribute parse_spec_attribute attrs
let extract_ignore_attribute attrs = extract_attribute parse_ignore_attribute attrs
