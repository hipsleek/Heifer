open Core
open Core.Syntax
open Core.Pretty
open Bindlib
open Util.Strings

let pp_term ppf t = if !Prover_options.notation then pp_term ppf t else dump_term ppf t

type t = {
  rename_ctxt : Rename.ctxt;
  constants : term var SMap.t;
  assumptions : term SMap.t;
  heap_assumptions : term list; (* TODO: add names *)
  goal : term;
}

let create ~goal =
  {
    rename_ctxt = Rename.empty_ctxt;
    constants = SMap.empty;
    assumptions = SMap.empty;
    heap_assumptions = [];
    goal;
  }

let pp_constants pp_name ppf constants =
  let constants = List.map fst (SMap.bindings constants) in
  match constants with
  | [] -> ()
  | _ -> Fmt.pf ppf "@[<hov>%a@]@," (Fmt.list ~sep:Fmt.comma pp_name) constants

let pp_assumptions_ne pp_name pp_assumption ppf assumptions =
  Fmt.pf ppf "@[<v>%a@]@,"
    (Fmt.list (Fmt.hovbox ~indent:2 (Fmt.pair ~sep:(Fmt.any ": ") pp_name pp_assumption)))
    (SMap.bindings assumptions)

let pp_line ppf = Fmt.pf ppf "%s@," (draw_line !Prover_options.line_length)

let pp_assumptions pp_name pp_assumption ppf assumptions =
  if not (SMap.is_empty assumptions) then pp_assumptions_ne pp_name pp_assumption ppf assumptions;
  pp_line ppf

let pp_heap_line ppf = Fmt.pf ppf "%s@," (draw_line (pred !Prover_options.line_length) ^ "*")
let pp_heap_assumptions_ne pp_heap_assumption ppf = Fmt.pf ppf "%a@," (Fmt.list pp_heap_assumption)

let pp_heap_assumptions pp_heap_assumption ppf heap_assumptions =
  if not (List.is_empty heap_assumptions) then begin
    pp_heap_assumptions_ne pp_heap_assumption ppf heap_assumptions;
    pp_heap_line ppf
  end

let pp_goal pp_term ppf = function
  | Subsumes (lhs, rhs) -> Fmt.pf ppf "   %a@,<: %a" pp_term lhs pp_term rhs
  | goal -> Fmt.pf ppf "%a" pp_term goal

let pp ppf { rename_ctxt = _; constants; assumptions; heap_assumptions; goal } =
  (* TODO: pp_term_in rename_ctxt *)
  Fmt.pf ppf "@[<v>";
  pp_constants Fmt.string ppf constants;
  pp_assumptions Fmt.string pp_term ppf assumptions;
  pp_heap_assumptions pp_term ppf heap_assumptions;
  pp_goal pp_term ppf goal;
  Fmt.pf ppf "@]"
