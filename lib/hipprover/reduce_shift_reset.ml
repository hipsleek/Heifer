open Hipcore_typed
open Typedhip
open Debug
(*
open Pretty
open Subst
*)

open Utils

(* shift-reset reduction rules. Technically we can put this in normalize.ml; but
   let's put this logic into a separate files for easy of understanding *)

(* a visitor *)
let shift_free () = Misc.todo ()

let reset_free () = Misc.todo ()

(* do we need this tho? Seems redundant! *)
let shift_reset_free () = Misc.todo ()

let get_cont_body (cont : term) : staged_spec =
  match cont.term_desc with
  | TLambda (_, _, body, _) ->
      begin match body with
      | Some body -> body
      | None -> failwith "get_cont_body: empty body"
      end
  | _ ->
      failwith "get_cont_body: not a TLambda"

let get_cont_args (cont : term) : binder list =
  match cont.term_desc with
  | TLambda (_, args, _, _) -> args
  | _ -> failwith "get_cont_args: not a TLambda"

let get_cont_arg (cont : term) : binder =
  match get_cont_args cont with
  | [arg] -> arg
  | [] -> failwith "get_cont_arg: empty arg"
  | _ -> failwith "get_cont_arg: multiple args"

let set_cont_body ({term_desc; term_type} : term) (body : staged_spec) : term =
  match term_desc with
  | TLambda (name, args, _, code) -> {term_desc = TLambda (name, args, Some body, code); term_type}
  | _ -> failwith "set_cont_body: not a TLambda"

let set_cont_arg ({term_desc; term_type} : term) (arg : binder) : term =
  match term_desc with
  | TLambda (name, _, body, code) -> {term_desc = TLambda (name, [arg], body, code); term_type}
  | _ -> failwith "set_cont_arg: not a TLambda"

let ignored_cont_arg = "#ignored_arg"

let is_ignored_cont_binder (b : binder) : bool =
  ident_of_binder b = ignored_cont_arg

let fold_cont_desc (cont : term_desc) (var_case : string -> 'a) (lam_case : binder -> staged_spec -> 'a) : 'a =
  match cont with
  | Var k ->
      var_case k
  | TLambda (_, args, body_opt, _) ->
      let arg = match args with
        | [] -> failwith "fold_cont_desc: empty arg"
        | [arg] -> arg
        | _ -> failwith "fold_cont_desc: too many args"
      in
      let body = match body_opt with
        | None -> failwith "fold_cont_desc: empty body"
        | Some body -> body
      in
      lam_case arg body
  | _ ->
      failwith "fold_cont_desc: not a TLambda or Var"

let compose_cont_desc (f : staged_spec) (cont : term_desc) : staged_spec =
  let var_case k =
    let imm = Variables.fresh_variable ~v:"v" "" in
    let arg = Syntax.var imm in
    Bind ((imm, arg.term_type), f, HigherOrder (k, [arg]))
  in
  let lam_case arg body =
    if is_ignored_cont_binder arg then Sequence (f, body) else Bind (arg, f, body)
  in
  fold_cont_desc cont var_case lam_case

let compose_cont (f : staged_spec) (arg : binder) (cont : term) : term =
  let body = compose_cont_desc f cont.term_desc in
  {term_desc = TLambda ("", [arg], Some body, None); term_type = Lamb}

(* reset (forall x. f) \entails forall x. reset f *)
(* only on the left *)
let norm_reset_all : _ Rewriting2.rule = Rewriting2.(
  reset (forall __ __) __,
  fun x f cont -> ForAll (x, Reset (f, cont))
)

(* reset (exists x. f) \bientails exists x. reset f *)
(* bientails; both side of the proof *)
let norm_reset_ex : _ Rewriting2.rule = Rewriting2.(
  reset (exists __ __) __,
  fun x f cont -> Exists (x, Reset (f, cont))
)

(* reset (f1 \/ f2) \bientails reset f1 \/ reset f2 *)
(* bientails; both side of the proof *)
let norm_reset_disj : _ Rewriting2.rule = Rewriting2.(
  reset (disj __ __) __,
  fun f1 f2 cont -> Disjunction (Reset (f1, cont), Reset (f2, cont))
)

(* reset (ens Q; f) \bientails ens Q; reset f *)
(* bientails; both side of the proof *)
(* let norm_reset_seq_ens : _ Rewriting2.rule = Rewriting2.(
  reset (seq (ens __ __) __) __ __,
  fun p k f x cont -> Sequence (NormalReturn (p, k), Reset (f, x, cont))
)

(* reset (req H; f) \entails req H; reset f *)
(* entails; only on the left *)
let norm_reset_seq_req : _ Rewriting2.rule = Rewriting2.(
  reset (seq (req __ __) __) __ __,
  fun p k f x cont -> Sequence (Require (p, k), Reset (f, x, cont))
)

let norm_reset_bind_ens : _ Rewriting2.rule = Rewriting2.(
  reset (bind __ (ens __ __) __) __ __,
  fun x p k f xcont cont -> Bind (x, NormalReturn (p, k), Reset (f, xcont, cont))
)

let norm_reset_bind_req : _ Rewriting2.rule = Rewriting2.(
  reset (bind __ (req __ __) __) __ __,
  fun x p k f xcont cont -> Bind (x, Require (p, k), Reset (f, xcont, cont))
) *)

(* reset (ens Q) \bientails ens Q *)
(* both side of the proof *)
let norm_reset_ens : _ Rewriting2.rule = Rewriting2.(
  reset (ens __ __) __,
  fun p k cont ->
    let reset_body = NormalReturn (p, k) in
    let var_case f =
      let imm = Variables.fresh_variable ~v:"v" "" in
      let arg = Syntax.var imm in
      let body = HigherOrder (f, [arg]) in
      Bind ((imm, arg.term_type), reset_body, body)
    in
    let lam_case arg body =
      let body = match body with NormalReturn _ -> body | _ -> Reset (body, Syntax.mk_id_lambda ()) in
      if is_ignored_cont_binder arg then Sequence (reset_body, body) else Bind (arg, reset_body, body)
    in
    fold_cont_desc cont.term_desc var_case lam_case
)

(* both sides *)
let shift_reset_normalization_rules_both : _ Rewriting2.database = [
  norm_reset_ex;
  norm_reset_disj;
  (* norm_reset_seq_ens; *)
  (* norm_reset_bind_ens; *)
  norm_reset_ens;
]

(* lhs only *)
let shift_reset_normalization_rules_lhs_only : _ Rewriting2.database = [
  norm_reset_all;
  (* norm_reset_seq_req; *)
  (* norm_reset_bind_req; *)
]

(* we need a more "structure" way to compose the continuation *)
(* if the continuation is identity, we completely replace the continuation with the new continuation.
   but this can be handled by the normalization to rewrite the redundant equality away *)
(* if the continuation takes an argument, then we need to connect the old continuation with the new stage
   by a "bind" *)
(* if the continuation does not take an argument, then we connect the old continuation with the new stage
   by a "seq" *)

(* accumulate/build the continuation; with seq *)
(* reset (shift body cont; f) -> reset (shift body (cont; f)) *)
let red_bind_shift_extend : _ Rewriting2.rule = Rewriting2.(
  bind __ (shift __ __ __ __ __) __,
  fun x_bind is_shift x_body f_body x_cont f_cont f ->
    Shift (is_shift, x_body, f_body, x_cont, Bind (x_bind, f_cont, f))
)

let red_seq_shift_extend : _ Rewriting2.rule = Rewriting2.(
  seq (shift __ __ __ __ __) __,
  fun is_shift x_body f_body x_cont f_cont f ->
    Shift (is_shift, x_body, f_body, x_cont, Sequence (f_cont, f))
)

(*
(* shift, immediately surronded by reset, is eliminated *)
let red_reset_shift_elim : _ Rewriting2.rule = Rewriting2.(
  reset (shift __ __ __ __ __) __ __,
  fun is_shift x_body f_body x_cont f_cont x_cont' f_cont' ->
    let open Syntax in
    let cont_name = Variables.fresh_variable ~v:"cont" "refined continuation" in
    let cont = term (TLambda (cont_name, [x_cont], Some (Reset (f_cont, x_cont', f_cont')), None)) Lamb in
    let defun = Syntax.(ens ~p:(eq (Variables.res_var ~typ:Lamb) cont) ()) in
    let body = if is_shift then Reset (f_body, x_cont', f_cont') else f_body in
    Bind (x_body, defun, body)
)
*)

(* only on the left, because of req *)
let red_reset_bind : _ Rewriting2.rule = Rewriting2.(
  reset (bind __ __ __) __,
  fun b f1 f2 cont ->
    match f1 with
    | Require _
    | NormalReturn _ -> Bind (b, f1, Reset (f2, cont))
    | _ -> Reset (f1, compose_cont f2 b cont)
)

(* only on the left, because of req *)
let red_reset_seq : _ Rewriting2.rule = Rewriting2.(
  reset (seq __ __) __,
  fun f1 f2 cont ->
    match f1 with
    | Require _
    | NormalReturn _ -> Sequence (f1, Reset (f2, cont))
    | _ -> Reset (f1, compose_cont f2 (ignored_cont_arg, Any) cont)
)

let red_reset_shift : _ Rewriting2.rule = Rewriting2.(
  reset (shift __ __ __ __ __) __,
  fun is_shift x_body f_body _ _ cont ->
    (* cont can either be a lambda or a var! *)
    let var_case f =
      Syntax.(ens ~p:(eq (Variables.res_var ~typ:Lamb) (Syntax.var f ~typ:Lamb)) ())
    in
    let lam_case arg cont_body =
      let cont_body = Reset (cont_body, Syntax.mk_id_lambda ()) in
      let cont = {term_desc = TLambda ("", [arg], Some cont_body, None); term_type = Lamb} in
      Syntax.(ens ~p:(eq (Variables.res_var ~typ:Lamb) cont) ())
    in
    let defun = fold_cont_desc cont.term_desc var_case lam_case in
    let body = if is_shift then Reset (f_body, Syntax.mk_id_lambda ()) else f_body in
    Bind (x_body, defun, body)
)

(* only on lhs *)
(* let shift_reset_red_rules : _ Rewriting2.database = [
  red_bind_shift_extend;
  red_seq_shift_extend;
  red_reset_shift_elim;
] *)

let shift_reset_reduce_spec_with (type k)
  (rules : (staged_spec, k) Rewriting2.database) (spec : staged_spec) : staged_spec =
  let@ _ = Hipcore_typed.Globals.Timing.(time norm) in
  let@ _ =
    span (fun r -> debug
      ~at:1
      ~title:"shift_reset_reduction"
      "%s\n==>\n%s"
      (Pretty.string_of_staged_spec spec)
      (string_of_result Pretty.string_of_staged_spec r))
  in
  let spec = Rewriting2.(autorewrite staged rules spec) in
  spec

let shift_reset_reduction_rules_lhs : _ Rewriting2.database = [
  norm_reset_ex;
  norm_reset_disj;
  (* norm_reset_seq_ens; *)
  (* norm_reset_bind_ens; *)
  norm_reset_ens;
  norm_reset_all;
  (* norm_reset_seq_req; *)
  (* norm_reset_bind_req; *)
  (* red_bind_shift_extend;
  red_seq_shift_extend;
  red_reset_shift_elim; *)
  red_reset_seq;
  red_reset_bind;
  red_reset_shift;
]

let shift_reset_reduction_rules_rhs : _ Rewriting2.database = [
]

let shift_reset_reduce_spec_lhs = shift_reset_reduce_spec_with shift_reset_reduction_rules_lhs

let shift_reset_reduce_spec_rhs = shift_reset_reduce_spec_with shift_reset_reduction_rules_rhs
