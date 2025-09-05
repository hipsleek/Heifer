(* Functions for printing the typed AST. *)

open Hipcore_common
open Typedhip
open Types
open Utils.Hstdlib

type 'a to_document = 'a -> PPrint.document

let pp_call_like : 'a. 'a to_document -> ?sep:PPrint.document -> (string * 'a list) to_document =
    let open PPrint in
    fun arg_fmt ?(sep = comma ^^ break 1) (f, args) ->
      group (string f ^^ parens (nest 2 (flow sep (List.map arg_fmt args))))

(** The main set of pretty-printing functions.

 We use records-as-objects instead of classes to make it easier
 to dynamically stack modifications. *)
type pretty_printer = {
  pp_typ : pretty_printer -> printing_context -> typ to_document;
  pp_binder : pretty_printer -> printing_context -> binder to_document;
  pp_bin_op : pretty_printer -> printing_context -> bin_rel_op to_document;
  pp_bin_term_op : pretty_printer -> printing_context -> bin_term_op to_document;
  pp_constant : pretty_printer -> printing_context -> const to_document;
  pp_lambda_like : pretty_printer -> printing_context -> (binder list * staged_spec option * core_lang option) to_document;
  pp_term : pretty_printer -> printing_context -> term to_document;
  pp_core_lang : pretty_printer -> printing_context -> core_lang to_document;
  pp_staged_spec : pretty_printer -> printing_context -> staged_spec to_document;
  pp_kappa : pretty_printer -> printing_context -> kappa to_document;
  pp_pi : pretty_printer -> printing_context -> pi to_document;
  pp_state : pretty_printer -> printing_context -> state to_document;
  pp_pattern : pretty_printer -> printing_context -> pattern to_document;
}
and printing_context = {
  (** The "binding power" of the parent AST node, analogous to operator precedence.
    Printers for AST nodes that use parentheses to disambiguate between different nestings of operators
    can use this context to determine whether or not they should parenthesize their own output.
    (When unsure, it might be best to parenthesize anyway, for clarity.) *)
  ppc_parent_binding : binding_power
}
and binding_power = 
  (* Used to inform the child that the parent is irrelevant to deciding whether or not to parenthesize. *)
  | Negative_inf
  | Finite of int

let default_printing_context () = {
  ppc_parent_binding = Negative_inf
}

(** Returns [true] iff [a] denotes a lower binding power then [b]. *)
let lower_precedence a b =
  match a, b with
  | Negative_inf, Finite _ -> true
  | Finite x, Finite y when x < y -> true
  | _, _ -> false

let with_binding power pp_context =
  {pp_context with ppc_parent_binding = power}
  [@warning "-23"] (* suppress this, since more fields might be added to printing_context in the future *)

let parent_binding_power ctx = ctx.ppc_parent_binding

(** Wrap [doc] with parentheses if the given binding power [binding] is less than the binding power in [ctx]. *)
let parens_if_needed ctx binding doc =
  if lower_precedence binding (parent_binding_power ctx)
  then PPrint.parens doc
  else doc

let rec flatten_binary_syntax ~(destruct : 'a -> ('a * 'a) option) (node : 'a) : 'a list =
  match destruct node with
  | Some (a, b) -> (flatten_binary_syntax ~destruct a) @ (flatten_binary_syntax ~destruct b)
  | None -> [node]

(** Like [PPrint.infix], but, in normal mode, puts the infix operator after the newline, and sets
  an alignment point for the right operand. *)
let infix_on_newline b op lhs rhs =
  PPrint.(group (lhs ^^ break b ^^ op ^^ blank b ^^ align (nest 1 rhs)))

let rec flatten_unary_syntax_right ~(destruct : 'a -> ('b * 'a) option) (node : 'a) : 'b list * 'a =
  match destruct node with
  | Some (b, a) ->
      let remaining, a = flatten_unary_syntax_right ~destruct a in
      ([b] @ remaining, a)
  | None -> ([], node)

(** Tries to put [elems] on one line, separated by [op] (with [b] spaces before and after). If an
  element does not fit, place it (and the operator) on a separate line, aligned to the end of [op] (including spacing.) *)
let prefixed_list b op elems =
  let open PPrint in
  flow (break b ^^ op ^^ blank b) (List.map align elems)

let suffixed_list before after op elems =
  let open PPrint in
  flow (blank before ^^ op ^^ break after) (List.map align elems)

(* For some AST nodes (e.g. Construct, BinOp), we want to format them as infix operators
   depending on the name of the function being called. Check if this function name is
   one of those operators. *)
let is_infix f = 
  match f with
  | "::" | "+" | "-" | "*" | "=" | "&&" | "||" | ">" | "<" | ">=" | "<=" | "^" -> true
  | _ -> false

(** Given an AST node, break it up into subnodes as much as possible using [destruct], convert them
  into documents using [renderer], then combine them into one document using [prefixed_list] and the
  given spacing and separator. This is most useful for flattening the tree when encountering an
  associative operator. *)
let format_as_prefixed_list ?(spacing = 1) ~(sep : PPrint.document) ~(destruct : 'a -> ('a * 'a) option) ~(renderer : 'a to_document) : 'a to_document =
  fun node ->
    let elements = flatten_binary_syntax ~destruct node in
    let formatted = List.map renderer elements in
    prefixed_list spacing sep formatted

let format_as_suffixed_list ?(before = 0) ?(after = 1) ~(sep : PPrint.document) ~(destruct : 'a -> ('a * 'a) option) ~(renderer: 'a to_document) : 'a to_document =
  fun node ->
    let elements = flatten_binary_syntax ~destruct node in
    let formatted = List.map renderer elements in
    suffixed_list before after sep formatted

let conj = PPrint.string "/\\"
let disj = PPrint.string "\\/"
let sep_arrow = PPrint.string "->"
let sep_conj = PPrint.star
let implies = PPrint.string "=>"
let subsumes = PPrint.string "<:"
let pure_not = PPrint.tilde

let default_printer =
  let open PPrint in {
  pp_typ = begin fun self ctx t ->
    let open PPrint in
    match t with
    | Any -> string "any"
    | Unit -> string "unit"
    | Int -> string "int"
    | Bool -> string "bool"
    | TyString -> string "string"
    | Lamb -> string "(? -> ?)"
    | TVar v -> string "'" ^^ string v
    | TConstr (name, args) -> begin match args with
      | [] -> string name
      | [arg] -> (self.pp_typ self ctx arg) ^^ space ^^ string name
      | args -> parens (separate (comma ^^ break 1) (List.map (self.pp_typ self ctx) args)) ^^ space ^^ string name
    end
    | Arrow _ ->
      let args, ret = flatten_unary_syntax_right ~destruct:(function Arrow (a, b) -> Some (a, b) | _ -> None) t in
      prefixed_list 1 (string "->") (List.map (self.pp_typ self (ctx |> with_binding (Finite 20))) (args @ [ret]))
      |> parens_if_needed ctx (Finite 10)
  end;
  (* binders, bin ops and constants are atomic, and thus do not need parenthesization *)
  pp_binder = begin
    fun _self _ b -> string (ident_of_binder b)
  end;
  pp_bin_op = begin
    fun _self _ op -> match op with
    | GT -> string ">"
    | LT -> string "<"
    | EQ -> string "="
    | GTEQ -> string ">="
    | LTEQ -> string "<="
  end;
  pp_bin_term_op = begin
    fun _self _ op -> match op with
    | Plus -> string "+"
    | Minus -> string "-"
    | SConcat -> string "++"
    | TAnd -> string "&&"
    | TPower -> string "^"
    | TTimes -> string "*."
    | TDiv -> string "/"
    | TOr -> string "||"
    | TCons -> string "::"
  end;
  pp_constant = begin
    fun _self _ c -> match c with
    | ValUnit -> string "()"
    | Num n -> string (string_of_int n)
    | TStr s -> dquotes (string s)
    | Nil -> string "[]"
    | TTrue -> string "true"
    | TFalse -> string "false"
  end;
  pp_lambda_like = begin
    fun self ctx (args, spec, body) ->
      let func_token = string "fun" in
      let rendered_args = align ((List.map (self.pp_binder self ctx) args @ [string "->"]) |> flow (break 1)) in
      let rendered_spec = match spec with
        | Some spec -> 
            let spec_open = string "(*@" in
            let spec_close = string "@*)" in
            group (spec_open ^^ space ^^ align (group (self.pp_staged_spec self (ctx |> with_binding Negative_inf) spec ^^ break 1 ^^ spec_close)))
        | None -> empty
      in
      let rendered_body = match body with
        | Some body -> self.pp_core_lang self ctx body
        | None -> underscore
      in
      group (func_token ^^ blank 1 ^^ rendered_args ^^ nest 2 (break 1 ^^ rendered_spec ^^ break 1 ^^ rendered_body))
  end;
  pp_term = begin
    (* Relevant precedence levels for terms (higher = stronger binding power):
      - 120: TPower, SConcat, TCons
      - 110: TTimes, TDiv
      - 100: TPlus, TMinus
      - 90: TNot
      - 80: TAnd
      - 70: TOr *)
    (* TApp, Construct and TLambda all delimit their own children in other ways, so there's no need to parenthesize them *)
    fun self ctx t -> match t.term_desc with
    | Const c -> self.pp_constant self (ctx |> with_binding Negative_inf) c
    | Var s -> string s
    | Rel (op, a, b) -> 
        (* special case to print propositional equality using only one equal sign.
           this helps distinguish it from boolean equality in expressions like (n == 0) = true *)
        let rendered_op =
          match op with
          | EQ -> string "=="
          | _ -> self.pp_bin_op self ctx op
        in
        group (infix 2 1 rendered_op (self.pp_term self (ctx |> with_binding Negative_inf) a) (self.pp_term self (ctx |> with_binding Negative_inf) b))
    | BinOp (op, a, b) -> begin
        let self_precedence = Finite (match op with
          | TPower | SConcat | TCons -> 120
          | TTimes | TDiv -> 110
          | Plus | Minus -> 100
          | TAnd -> 80
          | TOr -> 70)
        in
        let rendered = match op with
          (* handle associative operators separately, to flatten them *)
          | TCons | SConcat | TTimes | Plus | TAnd | TOr ->
            format_as_prefixed_list ~sep:(self.pp_bin_term_op self ctx op)
                ~destruct:(fun t -> match t.term_desc with BinOp (o, lhs, rhs) when o = op -> Some (lhs, rhs) | _ -> None)
                ~renderer:(self.pp_term self (ctx |> with_binding self_precedence)) t
          | _ -> group (infix 2 1 (self.pp_bin_term_op self ctx op)
                  (self.pp_term self (ctx |> with_binding self_precedence) a)
                  (self.pp_term self (ctx |> with_binding self_precedence) b))
        in
        (* decide whether or not to wrap this in parentheses *)
        parens_if_needed ctx self_precedence rendered
    end
    | TNot t -> precede (string "not ") (self.pp_term self (ctx |> with_binding (Finite 90)) t)
    | TApp (f, args) -> pp_call_like (self.pp_term self (ctx |> with_binding Negative_inf)) (f, args)
    | Construct (f, args) ->
        (* we need some additional logic to improve output when the constructor has no args, or is an infix op *)
        begin
        match args with
        | [] -> string f
        | [a; b] when is_infix f ->
          (* the only possible infix op here is :: *)
          (* format this as if it's BinOp(TCons, a, b), with the proper precedence*)
          let infix_precedence = Finite 120 in
          group (infix 0 1 (string f) (self.pp_term self (ctx |> with_binding infix_precedence) a) (self.pp_term self (ctx |> with_binding infix_precedence) b))
        | _ -> pp_call_like (self.pp_term self (ctx |> with_binding Negative_inf)) (f, args)
        end
    | TLambda (_name, args, spec, body) ->
        (* if it does not fit into one line, first, break it as 
          fun (args...) ->
            (*@@ spec @@*)
            body
          the args can be broken up further, as long as they are aligned with the first one
          the spec can be broken up further, as long as it's aligned with the opening tag
        *)
        self.pp_lambda_like self (ctx |> with_binding Negative_inf) (args, spec, body) |> parens
        (* TODO shift_reset_progs/state_monad.ml generates a spec during debugging with lots of nested (fun k -> (*@ ens emp /\ res = (fun k -> ... ) @*))
           and it causes an ugly pyramid... is there a better way? *)
    | TTuple args -> ignore args; string "tup"
  end;
  pp_pattern = begin fun self ctx pat -> match pat.pattern_desc with
    | PAny -> underscore
    | PConstant c -> self.pp_constant self ctx c
    | PVar v -> self.pp_binder self ctx v
    | PAlias (pat, s) -> self.pp_pattern self ctx pat ^^ blank 1 ^^ string "as" ^^ blank 1 ^^ string s
    | PConstr (name, args) ->
      match args with
      | [] -> string name
      | [a; b] when is_infix name ->
        group (infix 0 1 (string name) (self.pp_pattern self ctx a) (self.pp_pattern self ctx b))
      | _ -> pp_call_like (self.pp_pattern self ctx) (name, args)
  end;
  pp_core_lang = begin fun self ctx core -> match core.core_desc with
    | CValue value -> self.pp_term self ctx value
    | CLet (b, c1, c2) ->
      let header = group (
        string "let" ^^ space ^^ (self.pp_binder self (ctx |> with_binding Negative_inf) b) ^^ space ^^ equals
          ^^ nest 2 (break 1 ^^ self.pp_core_lang self (ctx |> with_binding Negative_inf) c1
          ^^ break 1 ^^ string "in")
      ) in
      group (header ^^ break 1 ^^ self.pp_core_lang self (ctx |> with_binding Negative_inf) c2)
    | CSequence (c1, c2) -> group (infix 0 0 semi
      (self.pp_core_lang self (ctx |> with_binding Negative_inf) c1)
      (self.pp_core_lang self (ctx |> with_binding Negative_inf) c2))
    | CIfElse (cond, c1, c2) ->
        (* TODO a special case for if-else chains could be good here *)
        string "if" ^^ nest 2 (break 1 ^^ self.pp_pi self (ctx |> with_binding Negative_inf) cond)
        ^^ break 1 ^^ string "then" ^^ blank 1 ^^ nest 2 (self.pp_core_lang self (ctx |> with_binding Negative_inf) c1)
        ^^ break 1 ^^ string "else" ^^ blank 1 ^^ nest 2 (self.pp_core_lang self (ctx |> with_binding Negative_inf) c2)
    | CFunCall (f, args) ->
        (* for these function calls, we mirror OCaml syntax *)
        string f ^^ nest 2 (space ^^ flow (break 1) (List.map (self.pp_term self (ctx |> with_binding Negative_inf)) args))
        |> parens
    | CWrite (loc, v) -> string loc ^^ space ^^ string "<-" ^^ nest 2 (break 1 ^^ self.pp_term self (ctx |> with_binding Negative_inf) v)
    | CRef v -> string "ref" ^^ space ^^ parens (self.pp_term self (ctx |> with_binding Negative_inf) v)
    | CRead loc -> string "!" ^^ string loc
    | CAssert (p, k) ->
        (* follows how req/ens is formatted *)
        (string "assert") ^^ nest 2 (space ^^ parens (self.pp_state self (ctx |> with_binding Negative_inf) (p, k)))
    | CPerform (eff, arg) ->
        let arg = match arg with
          | Some arg -> self.pp_term self (ctx |> with_binding Negative_inf) arg
          | None -> string "()"
        in
        string "perform" ^^ (parens (string eff ^^ break 1 ^^ arg))
    | CMatch (handler_type, _tcl, e, handlers, cases) -> 
        let match_token =
          match handlers with
          | [] -> string "match"
          | _ -> match handler_type with
            | Deep -> string "match[s]" | Shallow -> string "match[d]"
        in
        let pp_case case =
          let pattern = self.pp_pattern self (ctx |> with_binding Negative_inf) case.ccase_pat in
          let guard = match case.ccase_guard with
            | Some guard -> blank 1 ^^ group (string "when" ^^ group (self.pp_term self (ctx |> with_binding Negative_inf) guard))
            | None -> empty
          in
          let expr = self.pp_core_lang self (ctx |> with_binding Negative_inf) case.ccase_expr in
          string "|" ^^ space ^^ align (group (
            group (pattern
              ^^ guard ^^ blank 1 ^^ string "->")
            ^^ nest 2 (break 1 ^^ expr)))
        in
        let pp_handler _ = 
          (* not sure what the right syntax here should be... *)
          string "[effect handler]"
        in
        group (
          group (
            match_token ^^ nest 2 (break 1 ^^ self.pp_core_lang self (ctx |> with_binding Negative_inf) e) ^^ break 1 ^^ string "with"
          )
          ^^ break 1 ^^
          separate (break 1) (List.map pp_case cases @ List.map pp_handler handlers)
        )
        |> parens (* match statements having no ending delimiter was a mistake in ocaml syntax... *)
    | CResume (args) ->
        string "resume" ^^ nest 2 (space ^^ flow (break 1) (List.map (self.pp_term self (ctx |> with_binding Negative_inf)) args))
    | CLambda (args, spec, body) -> parens (self.pp_lambda_like self (ctx |> with_binding Negative_inf) (args, spec, Some body))
    | CShift (not_zero, k, body) -> 
        let shift_ident = if not_zero then "shift" else "shift0" in
        string shift_ident ^^ space ^^ nest 2 (parens (self.pp_lambda_like self (ctx |> with_binding Negative_inf) ([k], None, Some body)))
    | CReset body -> string "reset" ^^ space ^^ nest 2 (parens (self.pp_core_lang self (ctx |> with_binding Negative_inf) body))
  end;
  pp_staged_spec = begin fun self ctx f ->
    (* precedence in the parser is exists/forall, disjunction, req, ens, fn, shift, reset, sequence, bind, parens *)
    (* 
      i observe that usually, specs take the form of disjunction of sequences of quantifiers of binds of req/ens/fn/shift/reset
      i want sequence -> quantify -> bind to naturally read like a string of lines
      so that's the natural precedence

      but i need to be careful, since bind-association isn't proven

      - 90: Sequencing
      - 80: Conjunction (used by state)
      - 70: Disjunction
      - 60: Bind?
    *)
    match f with
    (* try to put as many Exists/ForAll on one line as possible to improve output on chains of quantifiers *)
    | Exists _ | ForAll _ ->
        (* flatten syntax to extract any quantifier chain *)
        let quantifiers, body = flatten_unary_syntax_right
          ~destruct:(function Exists (b, s) -> Some (`Exists b, s) | ForAll (b, s) -> Some (`ForAll b, s) | _ -> None) f in
        let rendered_qs = List.map (fun v ->
          match v with
            | `Exists b -> concat [string "ex"; space; self.pp_binder self ctx b; dot]
            | `ForAll b -> concat [string "forall"; space; self.pp_binder self ctx b; dot]) quantifiers in
        (* print the body with parens and indent to make the scope of the bindings clear *)
        let rendered_body = parens (align (self.pp_staged_spec self (ctx |> with_binding Negative_inf) body)) in
        group (flow (break 1) rendered_qs ^^ nest 2 (break 1 ^^ rendered_body))
    | Require (p, k) ->
        (string "req") ^^ nest 2 (space ^^ parens (self.pp_state self (ctx |> with_binding Negative_inf) (p, k)))
    | NormalReturn (p, k) ->
        (string "ens") ^^ nest 2 (space ^^ parens (self.pp_state self (ctx |> with_binding Negative_inf) (p, k)))
    | HigherOrder (f, args) -> pp_call_like (self.pp_term self ctx) (f, args)
    | Disjunction _ -> 
      (* flatten the structure of a set of disjuncts, so they can always be rendered as a flat list *)
      let disj_precedence = Finite 70 in
      format_as_prefixed_list ~sep:disj
          ~destruct:(function Disjunction (s1, s2) -> Some (s1, s2) | _ -> None)
          ~renderer:(self.pp_staged_spec self (ctx |> with_binding disj_precedence)) f
      |> parens_if_needed ctx disj_precedence
    | Sequence _ ->
      (* group (infix 0 0 (semi ^^ blank 1) (self.pp_staged_spec self ctx s1) (self.pp_staged_spec self ctx s2)) *)
      let seq_precedence = Finite 90 in
      format_as_suffixed_list ~sep:semi
        ~destruct:(function Sequence (s1, s2) -> Some (s1, s2) | _ -> None)
        ~renderer:(self.pp_staged_spec self (ctx |> with_binding seq_precedence)) f
      |> parens_if_needed ctx seq_precedence
    | Bind (v, s1, s2) ->
    (* this can be rendered as:
      - if it fits into one line, (s1); v. s2
      - otherwise, render s2 on its own line
      - if the bound value doesn't fit, break into its own lines, and indent by two *)
        let bind_precedence = Finite 60 in
        let header = group (lparen ^^ nest 2 (break 0 ^^ self.pp_staged_spec self ctx s1) ^^ break 0 ^^ rparen ^^ semi
                            ^^ space ^^ (self.pp_binder self (ctx |> with_binding Negative_inf) v)) ^^ dot in
        let body = parens_if_needed ctx bind_precedence (self.pp_staged_spec self (ctx |> with_binding bind_precedence) s2) in
        group (header ^^ break 1 ^^ body)
    | Shift (non_zero, cont_binder, metacont, hole_binder, partial_cont) -> 
      let call_name = if non_zero then "shift" else "shift0" in
      (* special case to hide the partial continuation if it is just the identity (i.e. it has not absorbed
         any of the context yet) *)
      let partial_cont_is_empty = 
        match partial_cont with
        | NormalReturn (p, EmptyHeap) -> begin
          match Variables.eq_res_term p with
          | Some {term_desc = Var v; _} -> v = (ident_of_binder hole_binder)
          | _ -> false
          end
        | _ -> false
      in
      if partial_cont_is_empty
      then pp_call_like (self.pp_lambda_like self ctx) ~sep:(semi ^^ break 1)
        (call_name, [[cont_binder], Some metacont, None])
      else
        pp_call_like (self.pp_lambda_like self ctx) ~sep:(semi ^^ break 1)
        (call_name, [[cont_binder], Some metacont, None; [hole_binder], Some partial_cont, None])
    | Reset r ->
        angles (self.pp_staged_spec self ctx r)
    | _ -> string "[other stage]"
  end;
  pp_pi = begin
    fun self ctx p -> match p with
    (* precedences:
        - 100: Not
        - 90: Subsumption, atomics
        - 80: Conjunction
        - 70: Disjunction
        - 60: Implication
    *)
    (* precedence is True, False, atoms, (subsumes), conj, (disjunction), (implication), not, parens *)
    | True -> string "T"
    | False -> string "F"
    | And _ ->
        let and_precedence = Finite 80 in
        format_as_prefixed_list ~sep:conj
            ~destruct:(function And (p1, p2) -> Some (p1, p2) | _ -> None)
            ~renderer:(self.pp_pi self (ctx |> with_binding and_precedence)) p
        |> parens_if_needed ctx and_precedence
   | Or _ -> 
       let or_precedence = Finite 70 in
        format_as_prefixed_list ~sep:disj
            ~destruct:(function Or (p1, p2) -> Some (p1, p2) | _ -> None)
            ~renderer:(self.pp_pi self (ctx |> with_binding or_precedence)) p
        |> parens_if_needed ctx or_precedence
    | Imply (p1, p2) -> 
        let imply_precedence = Finite 60 in
        infix 2 1 implies (self.pp_pi self (ctx |> with_binding imply_precedence) p1) 
          (self.pp_pi self (ctx |> with_binding imply_precedence) p2)
        |> parens_if_needed ctx imply_precedence
    | Not p -> 
        let not_precedence = Finite 100 in
        pure_not ^^ (self.pp_pi self (ctx |> with_binding not_precedence) p)
        |> parens_if_needed ctx not_precedence
    | Predicate (f, args) -> pp_call_like (self.pp_term self (ctx |> with_binding Negative_inf)) (f, args)
    | Atomic (op, a, b) -> 
        let atom_precedence = Finite 90 in
        infix 2 1 (self.pp_bin_op self ctx op) 
          (self.pp_term self (ctx |> with_binding atom_precedence) a)
          (self.pp_term self (ctx |> with_binding atom_precedence) b)
        |> parens_if_needed ctx atom_precedence
    | Subsumption (p1, p2) -> 
        let subsume_precedence = Finite 90 in
        infix 2 1 subsumes (self.pp_term self (ctx |> with_binding subsume_precedence) p1)
          (self.pp_term self (ctx |> with_binding subsume_precedence) p2)
        |> parens_if_needed ctx subsume_precedence
  end;
  pp_kappa = begin
    fun self ctx k -> match k with
    | EmptyHeap -> string "emp"
    | PointsTo (loc, v) -> group ((string loc) ^^ space ^^ sep_arrow ^^ break 1 ^^ (self.pp_term self ctx v))
    | SepConj _ ->
      format_as_prefixed_list ~sep:sep_conj
        ~destruct:(function SepConj (k1, k2) -> Some (k1, k2) | _ -> None)
        ~renderer:(self.pp_kappa self ctx) k
  end;
  pp_state = begin
    fun self ctx (p, k) ->
      let conj_precedence = Finite 80 in
      match (p, k) with
      (* special case to make return stages play nicely with indentation. related: github issue #31 *)
      | (Atomic (EQ, {term_desc = Var "res"; _}, t), EmptyHeap) ->
        group (string "res" ^^ blank 1 ^^ equals ^^ break 1 ^^ nest 2 (self.pp_term self (ctx |> with_binding conj_precedence) t))
      (* general case *)
      | _ -> infix_on_newline 1 conj (self.pp_pi self (ctx |> with_binding conj_precedence) p) 
              (self.pp_kappa self (ctx |> with_binding conj_precedence) k)
  end;
}

(** Modify the pretty printer to also output type annotations.

    {b Note}: This function is NOT idempotent; applying this multiple times
    will lead to type annotations being repeated in the output. *)
let add_type_annotations (pp : pretty_printer) : pretty_printer =
  let open PPrint in
  {
    pp with
    pp_binder = begin fun self ctx b ->
      group (parens (pp.pp_binder self (ctx |> with_binding Negative_inf) b ^^ space ^^ colon ^^ break 1 ^^ (self.pp_typ self ctx (type_of_binder b))))
    end;
    pp_term = begin fun self ctx t ->
      group (parens (pp.pp_term self (ctx |> with_binding Negative_inf) t ^^ space ^^ colon ^^ break 1 ^^ (self.pp_typ self ctx t.term_type)))
    end;
    pp_core_lang = begin fun self ctx core ->
      group (parens (pp.pp_core_lang self (ctx |> with_binding Negative_inf) core ^^ space ^^ colon ^^ break 1 ^^ (self.pp_typ self ctx core.core_type)))
    end
  }

(** {1 Printer configuration} *)

type config = {
  cfg_print_types : bool;
  cfg_print_spacing : bool;
  cfg_column_width : int;
  cfg_ribbon_width : float;
}

let default_config = {
  cfg_print_types = false;
  cfg_print_spacing = true;
  cfg_column_width = 80;
  cfg_ribbon_width = 1.0
}

let current_config_ = ref default_config

let current_config () = !current_config_

let set_current_config f = current_config_ := f !current_config_

let set_single_line ?(enabled = true) cfg = {cfg with cfg_print_spacing = not enabled}
let set_types_display ?(enabled = true) cfg = {cfg with cfg_print_types = enabled}
let set_column_width w cfg = {cfg with cfg_column_width = w}

let pp_with_config cfg pp =
  if cfg.cfg_print_types
  then add_type_annotations pp
  else pp

(** { 1 Printing functions }*)

module type Printers_internal = sig
  val pp_staged_spec : staged_spec to_document
  val pp_binder : binder to_document 
  val pp_typ : typ to_document 
  val pp_term : term to_document 
  val pp_pi : pi to_document 
  val pp_kappa : kappa to_document 
  val pp_state : state to_document 
  val pp_pattern : pattern to_document 
  val pp_core_lang : core_lang to_document 
end

let obtain_printers_internal cfg : (module Printers_internal) =
  let ctx = default_printing_context () in
  let pp = pp_with_config cfg default_printer in
  (module struct
    let pp_staged_spec f = pp.pp_staged_spec pp ctx f
    let pp_binder f = pp.pp_binder pp ctx f
    let pp_typ t = pp.pp_typ pp ctx t
    let pp_term t = pp.pp_term pp ctx t
    let pp_pi p = pp.pp_pi pp ctx p
    let pp_kappa k = pp.pp_kappa pp ctx k
    let pp_state st = pp.pp_state pp ctx st
    let pp_pattern pat = pp.pp_pattern pp ctx pat
    let pp_core_lang core = pp.pp_core_lang pp ctx core
  end)

let print_document cfg doc =
  let buf = Buffer.create 256 in
  begin
    if cfg.cfg_print_spacing
    then PPrint.ToBuffer.pretty cfg.cfg_ribbon_width cfg.cfg_column_width buf doc
    else PPrint.ToBuffer.compact buf doc
  end;
  Buffer.contents buf

let string_of_binder ?config b =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_binder b |> print_document config

let string_of_type ?config t =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_typ t |> print_document config

let string_of_pi ?config p =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_pi p |> print_document config

let string_of_kappa ?config k =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_kappa k |> print_document config

let string_of_state ?config st =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_state st |> print_document config

let string_of_pattern ?config pat =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_pattern pat |> print_document config

let string_of_term ?config t =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_term t |> print_document config

let string_of_core_lang ?config core =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_core_lang core |> print_document config

let string_of_staged_spec ?config f =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  M.pp_staged_spec f |> print_document config

let string_of_option ?(none = "") some opt =
  match opt with
  | Some v -> some v
  | None -> none

let string_of_list ?(sep=", ") pp elems =
  List.map pp elems |> String.concat sep

let string_of_pred ?config pred =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  let open PPrint in
  pp_call_like M.pp_binder (pred.p_name, pred.p_params) ^^ space ^^ equals ^^ nest 2 (break 1 ^^ M.pp_staged_spec pred.p_body)
  |> print_document config

let string_of_type_declaration ?config tdecl =
  let config = Option.value config ~default:(current_config ()) in
  let module M = (val obtain_printers_internal config : Printers_internal) in
  let open PPrint in
  let pp_inductive constrs =
    let pp_constr (name, arg_types) =
      if List.is_empty arg_types
      then string name
      else (string name) ^^ string "of" ^^ prefixed_list 1 (string "*") (List.map M.pp_typ arg_types)
    in
    prefixed_list 1 (string "|") (List.map pp_constr constrs)
  in
  let pp_record _r = string "record" in
  let pp_kind kind =
    match kind with
    | Tdecl_inductive constrs -> pp_inductive constrs
    | Tdecl_record r -> pp_record r
  in
  group (string "type" ^^ space ^^ M.pp_typ (TConstr (tdecl.tdecl_name, tdecl.tdecl_params)) ^^ space ^^ break 1 ^^
    pp_kind tdecl.tdecl_kind)
  |> print_document config
    
let pp_assoc_list pp_key pp_value m =
  let open PPrint in
  let pp_element (k, v) = 
    (pp_key k) ^^ space ^^ string "->" ^^ space ^^ (pp_value v)
  in
  braces (flow (semi ^^ blank 1) (List.map pp_element m))

let string_of_abs_env ?(config = default_config) abs_env =
  let module M = (val obtain_printers_internal config : Printers_internal) in
  let open PPrint in
  let variable_types = abs_env.vartypes |> SMap.bindings in
  let type_eqs = (TMap.map (fun t -> U.get t) !(abs_env.equalities)) |> TMap.bindings in
  brackets (group (string "vars:" ^^ space ^^ pp_assoc_list string M.pp_typ variable_types ^^ comma ^^ break 1
    ^^ string "eqs:" ^^ pp_assoc_list M.pp_typ M.pp_typ type_eqs))
  |> print_document config

(* tests *)

let%expect_test "syntax of output" =
  let int_var v = {term_desc = Var v; term_type = Int} in
  let cint c = {term_desc = Const (Num c); term_type = Int} in
  let (+~) a b = {term_desc = BinOp (Plus, a, b); term_type = Int} in
  let (=~) a b = Atomic (EQ, a, b) in
  let f1 = NormalReturn (int_var "res" =~ cint 0, EmptyHeap) in
  print_string (string_of_staged_spec ~config:(default_config |> set_types_display) f1);
  [%expect {| ens (res = (0 : int)) |}];

  (* f2 can be any output long enough to force default Format behavior to break lines *)
  let to_sum = List.init 20 Fun.id |> List.map cint in
  let f2 = NormalReturn (int_var "res" =~ List.fold_left (+~) (cint 0) to_sum, EmptyHeap) in
  print_string (string_of_staged_spec ~config:(default_config |> set_single_line) f2);
  [%expect {| ens (res = 0 + 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12 + 13 + 14 + 15 + 16 + 17 + 18 + 19) |}];

  (* now test that the column width can change the output *)
  print_string (string_of_staged_spec ~config:(default_config |> set_column_width 20) f2);
  [%expect {|
    ens (res =
      0 + 0 + 1 + 2 + 3
        + 4 + 5 + 6 + 7
        + 8 + 9 + 10
        + 11 + 12 + 13
        + 14 + 15 + 16
        + 17 + 18 + 19)
    |}];

  let subpat = List.init 40 (Fun.const {pattern_desc = PAny; pattern_type = Int}) in
  let p1 = {pattern_desc = PConstr ("with_lots_of_arguments", subpat); pattern_type = TConstr ("big_type", [])} in
  Format.printf "expanded: %s\ncompacted: %s\n" (string_of_pattern p1) (string_of_pattern ~config:(default_config |> set_single_line) p1);
  [%expect {|
    expanded: with_lots_of_arguments(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _)
    compacted: with_lots_of_arguments(_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _)
    |}];

  let t = (cint 1 +~ cint 2) in
  Format.printf "expanded: %s\n" (string_of_term t);
  [%expect {| expanded: 1 + 2 |}];;
