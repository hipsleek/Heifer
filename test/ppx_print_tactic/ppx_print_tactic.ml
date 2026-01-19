open Ppxlib

let add_print s =
  match s.pstr_desc with
  | Pstr_eval _ ->
      let str = Format.asprintf "%a@." Pprintast.structure_item s in
      let str = String.sub str 2 (String.length str - 2) |> String.trim in
      let loc = s.pstr_loc in
      let open Ast_builder.Default in
      let expr =
        pexp_apply ~loc
          (pexp_ident ~loc { loc; txt = Lident "print_endline" })
          [(Nolabel, pexp_constant ~loc (Pconst_string (str, loc, None)))]
      in
      let s1 = pstr_eval ~loc expr [] in
      [s1; s]
  | _ -> [s]

let transform_impl str = List.concat_map add_print str
let () = Driver.register_transformation ~impl:transform_impl "get_meta_print"
