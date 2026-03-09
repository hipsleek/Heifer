type pattern =
  | PVar of string
  | PConstr of string * pattern list
  | PAny
  | PInt of int

type expr =
  | Var of string
  | Int of int
  | Fun of string list * expr
  | Apply of expr * expr list
  | Let of string * expr * expr
  | If of expr * expr * expr
  | Sequence of expr * expr
  | Shift of string * expr
  | Reset of expr
  | Perform of string * expr option
  | Resume of expr list
  | Match of expr * (pattern * expr) list
  | WithSpec of expr * string * string

type verification_unit = {
  pure_functions : (string * expr) list;
  program_functions : (string * expr) list;
}

let rec dump_pattern ppf p =
  match p with
  | PVar x -> Format.fprintf ppf "%S" x
  | PConstr (c, args) ->
      Format.fprintf ppf "%s(%a)" c
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ") dump_pattern)
        args
  | PAny -> Format.fprintf ppf "_"
  | PInt i -> Format.fprintf ppf "%d" i

let rec dump_term ppf t =
  match t with
  | Var x -> Format.fprintf ppf "Var %S" x
  | Int i -> Format.fprintf ppf "Int %d" i
  | Fun (xs, body) ->
      Format.fprintf ppf "Fun ([%a], %a)"
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
           (fun ppf x -> Format.fprintf ppf "%S" x))
        xs dump_term body
  | Apply (f, args) ->
      Format.fprintf ppf "Apply (%a, [%a])" dump_term f
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ") dump_term)
        args
  | Let (x, t1, t2) -> Format.fprintf ppf "Let (%S, %a, %a)" x dump_term t1 dump_term t2
  | If (c, t1, t2) -> Format.fprintf ppf "If (%a, %a, %a)" dump_term c dump_term t1 dump_term t2
  | Sequence (t1, t2) -> Format.fprintf ppf "Sequence (%a, %a)" dump_term t1 dump_term t2
  | Shift (k, body) -> Format.fprintf ppf "Shift (%S, %a)" k dump_term body
  | Reset t -> Format.fprintf ppf "Reset (%a)" dump_term t
  | Perform (eff, arg) ->
      Format.fprintf ppf "Perform (%S, %a)" eff
        (fun ppf arg ->
          match arg with
          | None -> Format.fprintf ppf "None"
          | Some t -> Format.fprintf ppf "Some (%a)" dump_term t)
        arg
  | Resume args ->
      Format.fprintf ppf "Resume ([%a])"
        (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ") dump_term)
        args
  | Match (t, cases) ->
      Format.fprintf ppf "Match (%a, [%a])" dump_term t
        (Format.pp_print_list
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
           (fun ppf (p, e) -> Format.fprintf ppf "(%a, %a)" dump_pattern p dump_term e))
        cases
  | WithSpec (t, s, name) -> Format.fprintf ppf "WithSpec (%a, %S, %S)" dump_term t s name
