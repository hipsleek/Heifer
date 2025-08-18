open Typedhip
open Syntax
open Hipcore.Common
open Hipcore.Types
open Hipcore.Variables
open Rewrite_context

type 'a subst_context =
  | Sctx_staged : staged_spec subst_context
  | Sctx_term : term subst_context
  | Sctx_pure : pi subst_context
  | Sctx_heap : kappa subst_context

(* helpers to delegate visitor calls to the right method given a subst_context *)

type 'env map_visitor_type = <
  visit_staged_spec : 'mono. 'env -> staged_spec -> staged_spec;
  visit_pi : 'mono. 'env -> pi -> pi;
  visit_kappa : 'mono. 'env -> kappa -> kappa;
  visit_term : 'mono. 'env -> term -> term;
>

let map_visitor_function (type ctx_type) map_visitor (ctx_type : ctx_type subst_context)
  : 'env -> ctx_type -> ctx_type =
  let visitor = (map_visitor :> 'env map_visitor_type) in
  match ctx_type with
  | Sctx_staged -> visitor#visit_staged_spec
  | Sctx_term -> visitor#visit_term
  | Sctx_heap -> visitor#visit_kappa
  | Sctx_pure -> visitor#visit_pi

type ('env, 'result) reduce_visitor_type = <
  visit_staged_spec : 'mono. 'env -> staged_spec -> 'result;
  visit_pi : 'mono. 'env -> pi -> 'result;
  visit_kappa : 'mono. 'env -> kappa -> 'result;
  visit_term : 'mono. 'env -> term -> 'result;
>

let reduce_visitor_function (type ctx_type) reduce_visitor (ctx_type : ctx_type subst_context)
  : 'env -> ctx_type -> 'result =
  let visitor = (reduce_visitor :> ('env, 'result) reduce_visitor_type) in
  match ctx_type with
  | Sctx_staged -> visitor#visit_staged_spec
  | Sctx_term -> visitor#visit_term
  | Sctx_heap -> visitor#visit_kappa
  | Sctx_pure -> visitor#visit_pi

(* TODO is it possible to instead use an API that doesn't mix term substitutions with
   heap location/HOF substitutions? *)

let find_non_term_binding x bindings =
  match List.assoc_opt x bindings with
  | Some {term_desc = Var name; _} -> name
  | _ -> x

let types_of_free_vars (type ctx_type) (ctx_type : ctx_type subst_context) (ctx : ctx_type) =
  let visitor =
    object (_)
      inherit [_] reduce_spec as super
      method zero = SMap.empty
      method plus = SMap.merge_right_priority

      method! visit_Exists () x f =
        let b = super#visit_Exists () x f in
        SMap.remove (ident_of_binder x) b

      method! visit_ForAll () x f =
        let b = super#visit_ForAll () x f in
        SMap.remove (ident_of_binder x) b

      method! visit_TLambda () h ps sp b =
        let b = super#visit_TLambda () h ps sp b in
        List.fold_right (fun c t -> SMap.remove (ident_of_binder c) t) ps b

      method! visit_Bind () x f1 f2 =
        let b = super#visit_Bind () x f1 f2 in
        SMap.remove (ident_of_binder x) b

      method! visit_HigherOrder () f v =
        let b = super#visit_HigherOrder () f v in
        SMap.add f None b

      method! visit_term () t =
        match t.term_desc with
        | Var v -> SMap.singleton v (Some t.term_type)
        | _ -> super#visit_term () t

    end
  in
  reduce_visitor_function visitor ctx_type () ctx

let free_vars (type ctx_type) (ctx_type : ctx_type subst_context) (ctx : ctx_type) =
  let types_of_vars = types_of_free_vars ctx_type ctx in
  types_of_vars |> SMap.to_seq |> Seq.map fst |> SSet.of_seq

let subst_free_vars_in (type ctx_t) (ctx_type : ctx_t subst_context) (bindings : (string * term) list) (ctx : ctx_t) =
  let free_in_term =
    List.map (fun (_, t) -> free_vars Sctx_term t) bindings
    |> SSet.concat
  in
  (* Rename a free variable if [filter] is true. The expected use is to
   rename a binder in a rewritten term's context to avoid the rewritten term
   getting captured by the binder. *)
  let avoid_capture filter substitutor var node =
    let vari = ident_of_binder var in
    let (_, var_typ) = var in
    if filter
    then
      let new_var = fresh_variable ~v:vari () in
      (new_var, var_typ), substitutor [(vari, v new_var)] node
    else
      var, node
  in
  let subst_visitor = object (self)
    inherit [_] map_spec_with_binders as super

    method! visit_Var (env, bindings) v =
      match List.assoc_opt v bindings with
        | Some t when not (is_bound env v) -> t.term_desc
        | _ -> Var v

    method! visit_PointsTo (env, bindings) loc value =
      let new_name = find_non_term_binding loc bindings in
      super#visit_PointsTo (env, bindings) new_name value

    method! visit_HigherOrder (env, bindings) f args =
      let new_name = find_non_term_binding f bindings in
      super#visit_HigherOrder (env, bindings) new_name args

    method! visit_Exists (env, bindings) x f =
      let x, f = avoid_capture (SSet.mem (ident_of_binder x) free_in_term) (fun bindings -> self#visit_staged_spec (env, bindings)) x f in
      super#visit_Exists (env, bindings) x f

    method! visit_ForAll (env, bindings) x f =
      let x, f = avoid_capture (SSet.mem (ident_of_binder x) free_in_term) (fun bindings -> self#visit_staged_spec (env, bindings)) x f in
      super#visit_ForAll (env, bindings) x f

    method! visit_Bind (env, bindings) x f1 f2 =
      let x, f2 = avoid_capture (SSet.mem (ident_of_binder x) free_in_term) (fun bindings -> self#visit_staged_spec (env, bindings)) x f2 in
      super#visit_Bind (env, bindings) x f1 f2

    method! visit_Shift (env, bindings) nz k body x cont =
      let k, body = avoid_capture (SSet.mem (ident_of_binder k) free_in_term) (fun bindings -> self#visit_staged_spec (env, bindings)) k body in
      let x, cont = avoid_capture (SSet.mem (ident_of_binder k) free_in_term) (fun bindings -> self#visit_staged_spec (env, bindings)) x cont in
      super#visit_Shift (env, bindings) nz k body x cont

    method! visit_TLambda (env, bindings) name params spec body =
      let params, (spec, body) = Utils.Lists.map_state (fun (spec, body) param -> 
        avoid_capture (SSet.mem (ident_of_binder param) free_in_term) 
          (fun bindings (spec, body) -> (Option.map (self#visit_staged_spec (env, bindings)) spec,
            Option.map (self#visit_core_lang (env, bindings)) body)) param (spec, body)) (spec, body) params in
      super#visit_TLambda (env, bindings) name params spec body

    method! visit_CLambda (env, bindings) params spec body =
      let params, (spec, body) = Utils.Lists.map_state (fun (spec, body) param -> 
        avoid_capture (SSet.mem (ident_of_binder param) free_in_term) 
          (fun bindings (spec, body) -> (Option.map (self#visit_staged_spec (env, bindings)) spec,
            self#visit_core_lang (env, bindings) body)) param (spec, body)) (spec, body) params in
      super#visit_CLambda (env, bindings) params spec body


  end
  in
  visit_using_env (map_visitor_function subst_visitor ctx_type) bindings ctx

let subst_free_vars_term = subst_free_vars_in Sctx_term
let subst_free_vars = subst_free_vars_in Sctx_staged

let type_subst_visitor = object
  inherit [_] map_spec

  method! visit_TVar bindings v =
    match List.assoc_opt v bindings with
    | Some t -> t
    | None -> TVar v

end

let subst_types (type ctx_t) (ctx_type : ctx_t subst_context) (bindings : (string * typ) list) (ctx : ctx_t) =
  map_visitor_function type_subst_visitor ctx_type bindings ctx

let subst_types_in_type (bindings : (string * typ) list) (ctx : typ) =
  type_subst_visitor#visit_typ bindings ctx

let free_type_vars (type ctx_type) (ctx_type : ctx_type subst_context) (ctx : ctx_type) =
  let visitor =
    object (_)
      inherit [_] reduce_spec
      method zero = SSet.empty
      method plus = SSet.union

      method! visit_TVar () x = SSet.singleton x
    end
  in
  reduce_visitor_function visitor ctx_type () ctx

let%expect_test "subst" =
  let open Pretty in
  reset_counter 0;
  let test bs f1 =
    let f2 = subst_free_vars bs f1 in
    Format.printf "(%s)%s = %s@." (string_of_staged_spec f1)
      (string_of_list
         (fun (x, t) -> Format.asprintf "%s/%s" (string_of_term t) x)
         bs)
      (string_of_staged_spec f2)
  in
  let test_term bs f1 =
    let f2 = subst_free_vars_term bs f1 in
    Format.printf "(%s)%s = %s@." (string_of_term f1)
      (string_of_list
         (fun (x, t) -> Format.asprintf "%s/%s" (string_of_term t) x)
         bs)
      (string_of_term f2)
  in
  let v = v ~typ:Int in
  test_term [("z", v "a")] (v "z");
  [%expect {| (z)[a/z] = a |}];

  test [("z", v "a")] (HigherOrder ("x", [v "z"]));
  [%expect {| (x(z))[a/z] = x(a) |}];

  test [("x", v "y")] (HigherOrder ("x", [v "z"]));
  [%expect {| (x(z))[y/x] = y(z) |}];

  (* capture-avoidance *)
  test
    [("x", v "y")]
    (seq
       [
         ens ~p:(eq (v "x") (v "x")) ();
         Exists (("x", Int), ens ~p:(eq (v "x") (num 1)) ());
       ]);
  [%expect {| (ens x=x; ex x. (ens x=1))[y/x] = ens y=y; ex x. (ens x=1) |}];

  test [("x", v "z")] (Exists (("z", Int), ens ~p:(eq (v "z") (v "x")) ()));
  [%expect {| (ex z. (ens z=x))[z/x] = ex z0. (ens z0=z) |}]
