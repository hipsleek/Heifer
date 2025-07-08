(* open Hipprover *)
(* we need to clean up the imports here *)
open Hipcore
module Debug = Debug
open Typedhip
open Common
open Pretty_typed
open Ocaml_compiler
open Asttypes
(* get rid of the alias *)
type string = label
open Debug
(* open Normalize *)
(** Re-export Env, since it gets shadowed by another declaration later on. *)
module Compiler_env = Env
open Utils.Misc

let file_mode = ref false
let test_mode = ref false
let tests_failed = ref false

(** List of definitions to insert before passing code to the OCaml frontend.
    Mark declarations that should not be converted into intermediates with [@@ignore]. *)
let ocaml_prelude = "
  let shift _ = failwith \"placeholder\" [@@ignore]
  let shift0 _ = failwith \"placeholder\" [@@ignore]
  let reset _ = failwith \"placeholder\" [@@ignore]
  let (-->) _ _ = failwith \"placeholder\" [@@ignore]
  let ( * ) _ _ = failwith \"placeholder\" [@@ignore]

"

(*
let debug_tokens str =
  let lb = Lexing.from_string str in
  let rec loop tokens =
    let tok = Lexer.token lb in
    match tok with
    | EOF -> List.rev (tok :: tokens)
    | _ -> loop (tok :: tokens)
  in
  let tokens = loop [] in
  let s = tokens |> List.map string_of_token |> String.concat " " in
  debug ~at:3 ~title:"debug tokens" "%s" s
*)

(*
let rec check_remaining_obligations original_fname lems preds obligations =
  let open Search in
  all ~name:"subsumption obligation"
    ~to_s:(fun obl -> string_of_pobl obl)
    obligations (fun (params, obl) ->
    let name =
      (* the name of the obligation appears in tests and should be deterministic *)
      let base = "sub_obl" in
      if Str.string_match (Str.regexp ".*_false$") original_fname 0
        then base ^ "_false" else base
    in
    if check_obligation name params lems preds obl
      then succeed
      else fail)

and check_obligation name params lemmas predicates (l, r) : bool =
  let@ _ =
    Debug.span
      (fun _ -> debug ~at:1 ~title:(Format.asprintf "checking obligation: %s" name) "")
  in
  let open Search in begin
  let res = Entail.check_staged_subsumption_disj name params [] lemmas predicates l r in
  report_result ~kind:"Obligation" ~given_spec:r ~inferred_spec:r ~result:(Search.succeeded res) name;
  let* res = res in
  check_remaining_obligations name lemmas predicates res.subsumption_obl
  end |> Search.succeeded

let check_obligation_ name params lemmas predicates sub =
  check_obligation name params lemmas predicates sub |> ignore

let check_lambda_obligation_ name params lemmas predicates obl =
  let preds = SMap.merge_right_priority predicates obl.lo_preds in
  check_obligation_ name params lemmas preds (obl.lo_left, obl.lo_right)
*)

let test_failed result name =
  if String.ends_with ~suffix:"_false" name then
    result
  else not result

let indicate_if_test_failed result name =
  if test_failed result name then tests_failed := true

let expected_false result name =
  if not result && String.ends_with ~suffix:"_false" name then " (expected)" else ""

let report_header ~kind ~name =
  Format.sprintf "\n========== %s: %s ==========\n" kind name

let normal_report ~kind ~name ~inferred_spec ~given_spec ~result =
  let header = report_header ~kind ~name in
  let inferred_spec_string =
    Format.asprintf
      "[ Inferred specification ]\n%a\n"
      pp_staged_spec inferred_spec
  in
  let given_spec_string = match given_spec with
    | Some given_spec ->
        Format.asprintf
          "[ Given specification ]\n%a\n"
          pp_staged_spec given_spec
    | None ->
        ""
  in
  indicate_if_test_failed result name;
  let result_string =
    Format.sprintf "[ Entail Check ] %s%s\n"
      (string_of_bool result)
      (expected_false result name)
  in
  let report = String.concat "" [
    header;
    inferred_spec_string;
    given_spec_string;
    result_string;
  ] in
  debug ~at:2 ~title:"verification result" "";
  Format.printf "%s@." report

let truncate_name s =
  let l = String.length s in
  if l > 20 then
    String.sub s 0 7 ^ "..." ^ String.sub s (l-10) 10
  else s

let test_report ~kind ~name ~inferred_spec ~given_spec ~result =
  ignore (kind, inferred_spec, given_spec);
  indicate_if_test_failed result name;
  Format.printf "%20s: %s%s@." (truncate_name name) (string_of_bool result) (expected_false result name)

let report_result ~kind ~name ~inferred_spec ~given_spec ~result =
  let report = if !test_mode then test_report else normal_report in
  report ~kind ~name ~inferred_spec ~given_spec ~result;
  Globals.Timing.update_totals ()

let report_error ~kind ~name ~error =
  begin
    if !test_mode
    then
      Format.printf "%20s: error@." (truncate_name name)
    else begin
      print_string (report_header ~kind ~name);
      Format.printf "error occurred: %s (set DEBUG env var for details)\n" error
    end;
  end;
  Globals.Timing.update_totals ()

let infer_spec (prog : core_program) (meth : meth_def) =
  let open Hipprover.Forward_rules in
  let method_env = prog.cp_methods
    (* within a method body, params/locals should shadow functions defined outside *)
    |> List.filter (fun m -> meth.m_params |> List.assoc_opt m.m_name |> Option.is_some)
    (* treat recursive calls as abstract, as recursive functions should be summarized using predicates *)
    (* |> List.filter (fun m -> not (String.equal m.m_name meth.m_name)) *)
    |> List.map (fun m -> m.m_name, m)
    |> SMap.of_list
  in
  let pred_env = prog.cp_predicates in
  let fv_env = create_fv_env method_env pred_env in
  let inferred, _ = forward fv_env meth.m_body in
  inferred

let check_method prog inferred given =
  match given with
  | None -> true
  | Some given_spec ->
    let open Hipprover.Entail in
    (* likely that we need some env or extra setup later *)
    let pctx = create_pctx (Untypehip.untype_core_program prog) in
    check_staged_spec_entailment pctx (Untypehip.untype_staged_spec inferred) (Untypehip.untype_staged_spec given_spec)

let infer_and_check_method (prog : core_program) (meth : meth_def) (given_spec : staged_spec option) =
  let inferred_spec = infer_spec prog meth in
  let result = check_method prog inferred_spec given_spec in
  inferred_spec, result

let choose_spec (inferred_spec : staged_spec) (given_spec : staged_spec option) =
  Option.fold ~none:inferred_spec ~some:(fun spec -> spec) given_spec

let analyze_method (prog : core_program) (meth : meth_def) : core_program =
  let suppress_error_if_not_debug ~on_error ~default f =
    if Debug.in_debug_mode ()
    then f ()
    else
      try f ()
      with e ->
        on_error e;
        default
  in
  let@ _ = suppress_error_if_not_debug
    ~on_error:(fun e -> report_error ~kind:"Function" ~name:meth.m_name ~error:(Printexc.to_string e))
    ~default:prog in
  let given_spec = meth.m_spec in
  let inferred_spec, result =
    infer_and_check_method prog meth given_spec
  in
  (* after infference, if the method does not have a spec, then add
     the inferred spec into the method? *)
  let choosen_spec = choose_spec inferred_spec given_spec in
  let updated_meth = {meth with m_spec = Some choosen_spec} in
  (* we always add the method into the program, regardless of whether it is verified or not? *)
  let prog = {prog with cp_methods = updated_meth :: prog.cp_methods} in
  let prog =
    (* let@ _ = Globals.Timing.(time overall) in *)
    if not result then prog
    else begin
      let@ _ = Debug.span (fun _ -> debug
        ~at:2
        ~title:(Format.asprintf "remembering predicate for %s" meth.m_name)
        "")
      in
      let pred = Hipprover.Entail.derive_predicate meth.m_name 
        (List.map Untypehip.ident_of_binder meth.m_params)
        (Untypehip.untype_staged_spec inferred_spec)
        |> Retypehip.retype_pred_def in
      (* let pred = todo () in *)
      let cp_predicates = SMap.add meth.m_name pred prog.cp_predicates in
      {prog with cp_predicates}
      (* prog *)
    end
  in
  (* potentially report the normalized spec as well. Refactor *)
  report_result
    ~kind:"Function"
    ~name:meth.m_name
    ~inferred_spec
    ~given_spec
    ~result;
  prog

let check_lemma (prog : core_program) (l : lemma) : bool =
  let open Hipprover.Entail in
  let pctx = create_pctx (Untypehip.untype_core_program prog) in
  check_staged_spec_entailment pctx (Untypehip.untype_staged_spec l.l_left) (Untypehip.untype_staged_spec l.l_right)

let analyze_lemma (prog : core_program) (l : lemma) : core_program =
  let result = check_lemma prog l in
  (* we store the lemma regardless of whether or not it is provable *)
  let prog = {prog with cp_lemmas = SMap.add l.l_name l prog.cp_lemmas} in
  report_result
    ~kind:"Lemma"
    ~name:l.l_name
    ~inferred_spec:l.l_left
    ~given_spec:(Some l.l_right)
    ~result;
  prog

let process_logic_type_decl () = todo ()

let process_lemma () = todo ()

let process_method () = todo ()

let process_predicate () = todo ()

let process_pure_fn_info ({m_name; m_params; m_body; _}) = function
  | None -> ()
  | Some (_, ret_type) ->
      let pf : pure_fn_def =
      { pf_name = m_name;
        pf_params = m_params;
        pf_ret_type = ret_type;
        pf_body = m_body; }
      in
      Globals.define_pure_fn m_name pf

let process_intermediates (it : Typedhip.intermediate) prog : string list * core_program =
  (* Format.printf "%s\n" (Pretty.string_of_intermediate it);
  ([], prog) *)
  let open Typedhip in
  match it with
  (* | LogicTypeDecl (name, params, ret, path, lname) ->
      let def = {
        pft_name = name;
        pft_params = params;
        pft_ret_type = ret;
        pft_logic_name = lname;
        pft_logic_path = path
      }
      in
      Globals.global_environment.pure_fn_types <-
        SMap.add name def Globals.global_environment.pure_fn_types;
      [], prog *)
  | Typedef tdecl -> 
      Globals.define_type tdecl;
      debug ~at:1 ~title:"user type declaration" "%s" (Pretty.string_of_type_declaration tdecl);
      [], prog  
  | Eff _ ->
      todo ()
  | Lem l ->
      (* TODO: add obligation *)
      (* Format.printf "processing lemma\n"; *)
      (* debug ~at:4 ~title:(Format.asprintf "lemma %s" l.l_name) "%s" (string_of_lemma l); *)
      (* let left =
        let (f, ps) = l.l_left in
        let args, ret = unsnoc ps in
        function_stage_to_disj_spec f args ret
      in
      check_obligation_ l.l_name l.l_params prog.cp_lemmas prog.cp_predicates (left, [l.l_right]);
      debug ~at:4 ~title:(Format.asprintf "added lemma %s" l.l_name) "%s" (string_of_lemma l); *)
      (* add to environment regardless of failure *)
      (* we need to prove the lemma *)
      let@ _ = Debug.span (fun _ ->
        debug ~at:1 ~title:(Format.sprintf "verifying lemma: %s" l.l_name) "")
      in
      let prog = analyze_lemma prog l in
      [], prog
  | LogicTypeDecl _ ->
      process_logic_type_decl ()
  | Pred _p ->
    (*print_endline ("\n"^ p.p_name ^  Format.asprintf "(%s)" (String.concat ", " p.p_params) ^ ": ");
    print_endline (string_of_disj_spec p.p_body);
    *)
      (* let body' = replaceSLPredicatesWithDef p.p_body prog.cp_sl_predicates in
      let p' : pred_def = {
        p_name = p.p_name;
        p_params = p.p_params;
        p_body = Fill_type.fill_untyped_disj_spec body';
        p_rec = p.p_rec
      } *)
      (* in
      [], { prog with cp_predicates = SMap.add p'.p_name p' prog.cp_predicates } *)
      process_predicate ()
  | SLPred _p ->
      (* [], { prog with cp_sl_predicates = SMap.add p.p_sl_name p prog.cp_sl_predicates } *)
      todo ()
  | Meth (m_name, m_params, m_spec, m_body, m_tactics, pure_fn_info) ->
      let meth : meth_def = {m_name; m_params; m_spec; m_body; m_tactics} in
      process_pure_fn_info meth pure_fn_info;
      let@ _ = Debug.span (fun _ ->
        debug ~at:1 ~title:(Format.asprintf "verifying function: %s" meth.m_name) "")
      in
      let prog = analyze_method prog meth in
      [m_name], prog

let process_ocaml_structure (items: Ocaml_common.Typedtree.structure) : unit =
  let process_ocaml_item (bound_names, prog) item =
    match Ocamlfrontend.Core_lang_typed.transform_str bound_names item with
    | Some it ->
        let new_bound, prog = process_intermediates it prog in
        new_bound @ bound_names, prog
    | None ->
        bound_names, prog
  in
  ignore (List.fold_left process_ocaml_item ([], empty_program) items.str_items)

let run_ocaml_string s =
  (** Parse and typecheck the code, before converting it into a core language program.
     This mirrors the flow of compilation used in ocamlc. *)
  let s = ocaml_prelude ^ s in
  try
    let items = Parse.implementation (Lexing.from_string s) in
    let unit_info = Unit_info.(make ~source_file:"" Impl "") in
    Compile_common.with_info ~native:false ~tool_name:"heifer" ~dump_ext:"" unit_info @@ begin fun info ->
      let typed_implementation = Compile_common.typecheck_impl info items in
      let@ _ = Globals.Timing.(time overall_all) in
      process_ocaml_structure typed_implementation.structure
    end
  with
    | exn -> Format.printf "%a\n" Location.report_exception exn

(*
let mergeTopLevelCodeIntoOneMain (prog : intermediate list) : intermediate list =
  let rec helper li: (intermediate list  * core_lang list )=
    match li with
    | [] -> [], []
    | x :: xs  ->
        let nonMain, mainMeth = helper xs in
        begin match x with
        | Meth (nm, _, _, body, _, _) ->
            if String.compare nm "main" == 0
            then (nonMain, body :: mainMeth)
            else (x :: nonMain, mainMeth)
        | _ ->
            (x::nonMain, mainMeth)
        end
  in
  let nonMain, mainMeth = helper prog in
  let rec compose (main_segments: core_lang list) : core_lang =
    match main_segments with
    | [] -> CValue (Const ValUnit)
    | [x] -> x
    | x :: xs -> CLet ("_", x, compose xs)
 in
  nonMain @ [(Meth ("main", [], None, compose mainMeth, [], None ))]
*)

(* this is the entry of inputing the Racket file *)
let run_racket_string _s = ()
(*
  let open Racketfrontend in
  (* DARIUS: parsing should return a list of intermediate *)
  let core_program : intermediate list =
    Racket_parser.prog Racket_lexer.token (Lexing.from_string line) |> List.map Fill_type.fill_untyped_intermediate
  in
  let core_program : intermediate list = mergeTopLevelCodeIntoOneMain core_program in
  (* Format.printf "parsed racket program@.\n%s" (string_of_intermediate_list core_program); *)
  List.fold_left (fun t i ->
    let _bound, prog = process_intermediates i t in prog)
    empty_program core_program |> ignore
*)

let run_string kind s =
  (* disabled for now since prover backend is disabled as well *)
  (* Provers.handle (fun () -> *)
  (*   match kind with *)
  (*   | `Ocaml -> run_ocaml_string_ s *)
  (*   | `Racket -> run_racket_string_ s) *)
  match kind with
  | `Ocaml -> run_ocaml_string s
  | `Racket -> run_racket_string s

(* naive means of turning spec comments into attributes *)
let preprocess_spec_comments =
  let pattern = {|let \(.+\)\([
 ]*\)(\*@\([^@]+\)@\*)|} in
  let regex = Str.regexp pattern in
  fun text ->
    let@ _ =
      span (fun r ->
          debug ~at:3
            ~title:"preprocess_spec_comments"
            "%s\n---\n%s" text
            (string_of_result Fun.id r))
    in
    let output = Str.global_replace regex "let [@spec {|\\3|}] \\1\\2" text in
    output

let run_file input_file =
  let open Utils.Io in
  let chan = open_in input_file in
  let lines = input_lines chan in
  let content = String.concat "\n" lines in
  let content = preprocess_spec_comments content in
  let file_kind = get_file_type input_file in
  run_string file_kind content;
  close_in chan;
  if not !test_mode then begin
    let loc = List.length lines in
    let final_summary =
      "\n========== FINAL SUMMARY ==========\n"
      ^ "[   LoC   ] " ^ string_of_int loc ^ "\n"
      ^ "[    Z3   ] " ^ Format.asprintf "%.2f" (!Globals.Timing.z3_all/.1000.0) ^ " s\n"
      ^ "[   Why3  ] " ^ Format.asprintf "%.2f" (!Globals.Timing.why3_all/.1000.0) ^ " s\n"
      ^ "[   SMT   ] " ^ Format.asprintf "%.2f" (!Globals.Timing.provers_all/.1000.0) ^ " s\n"
      ^ "[  Total  ] " ^ Format.asprintf "%.2f" (!Globals.Timing.overall_all/.1000.0) ^ " s\n"
    in
    print_endline final_summary
  end

(*
let run_file input_file =
  let open Utils.Io in
  let chan = open_in input_file in
  let lines = input_lines chan in
  let content = String.concat "\n" lines in
  print_endline content;
  let open Parsing in
  let lexbuf = Lexing.from_string content in
  let staged_spec = Parser.parse_staged_spec Lexer.token lexbuf in
  print_endline (Pretty.string_of_staged_spec staged_spec)
*)

let main () =
  if Array.length (Sys.argv) < 2 then begin
    Format.printf "Usage: hip [input.ml|input.rkt]@.";
    exit 1
  end;
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
  run_file inputfile;
  if !test_mode && not !tests_failed then Format.printf "ALL OK!@.";
  exit (if !tests_failed then 1 else 0)
