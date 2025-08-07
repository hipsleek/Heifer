open Syntax
open Hipcore.Common
open Hipcore.Types
open Hipcore.Variables
open Typedhip
open Utils.Lists
open Utils.Lists.Monadic

type guarded_pattern = pattern * term

let make pat typ = {
  pattern_desc = pat;
  pattern_type = typ
}

let alias pat name = make (PAlias (pat, name)) pat.pattern_type

let pattern_of_constr ((name, args) : type_constructor) (constr_substitutions : (typ * typ) list) (pattern_type : typ) =
  (* all the extra parameters are needed to correctly reconstruct inner types *)
  make (PConstr (name, List.map (fun arg -> make PAny (instantiate_type_variables constr_substitutions arg)) args)) pattern_type

let rec free_vars_pat pat =
  (* return a type mapping since we need types of free variables when quantifying over them *)
  match pat.pattern_desc with
  | PAny | PConstant _ -> SMap.empty
  | PVar (name, typ) -> SMap.singleton name typ
  | PConstr (_, args) -> List.fold_right SMap.merge_arbitrary (List.map free_vars_pat args) SMap.empty
  | PAlias (pat, p) -> SMap.add p pat.pattern_type (free_vars_pat pat)

(** Return a set of patterns that match terms of the same type as [pat] such that
    - If a term does not match pat, it matches at least one pattern in this list.
    - If a term matches pat, it does not match any pattern in the list. *)
let rec complement pat =
    match pat.pattern_desc with
    | PAny | PVar _ -> []
    | PAlias (pat, name) -> complement pat |> List.map (fun pat -> alias pat name)
    | PConstr (name, args) ->
      let type_decl, _ = Globals.type_constructor_decl name in begin
      match type_decl.tdecl_kind with
      | Tdecl_record _ -> failwith "record patterns currently not implemented"
      | Tdecl_inductive constrs ->
        let self_complements =
          (* TODO we can make this more efficient by taking argument sets
             with only exactly one `Mismatch 
             this is at the cost of the return set no longer being disjoint *)
          args
          |> List.map (fun arg ->
            let complements = complement arg in
            (`Match arg) :: (List.map (fun pat -> `Mismatch pat) complements))
          |> Utils.Lists.cartesian_product
          |> List.filter (fun args -> List.exists (function `Mismatch _ -> true | _ -> false) args)
          |> List.map (List.map (function `Mismatch pat | `Match pat -> pat))
          |> List.map (fun args -> make (PConstr (name, args)) (pat.pattern_type))
        (* create patterns for all the other constructors *)
        in
        (* find what concrete types were used in the instantiation of this pattern's type variables *)
        (* we need this to correctly reconstruct types for the other constructors *)
        let concrete_types = match pat.pattern_type with
          | TConstr (_, args) -> args
          | _ -> assert false (* the type should be an ADT type *)
        in
        let type_substitutions = List.combine type_decl.tdecl_params concrete_types in 
        let other_constr_patterns =
          constrs
            |> List.filter (fun (other_name, _) -> name <> other_name)
            |> List.map (fun constr -> pattern_of_constr constr type_substitutions pat.pattern_type)
        in
        other_constr_patterns @ self_complements
      end
    | PConstant _ -> failwith "constant patterns currently not implemented"

let rec rename_bound_vars bindings pat =
  let rename_one v = SMap.find_opt v bindings in
  match pat.pattern_desc with
  | PAny | PConstant _ -> pat
  | PVar (v, _) -> begin
      match rename_one v with
      | Some renamed -> make (PVar renamed) pat.pattern_type
      | None -> pat
  end
  | PAlias (pat, p) -> begin
    match rename_one p with
    | Some renamed -> alias (rename_bound_vars bindings pat) (Untypehip.ident_of_binder renamed)
    | None -> pat
  end
  | PConstr (name, args) -> make (PConstr (name, List.map (rename_bound_vars bindings) args)) pat.pattern_type

let rec intersect_two p1 p2 = match p1.pattern_desc, p2.pattern_desc with
  | _, PAny -> return p1
  | PAny, _ -> return p2
  | _, PVar name -> return (alias p1 (Untypehip.ident_of_binder name))
  | PVar name, _ -> return (alias p2 (Untypehip.ident_of_binder name))
  | PAlias (p, s), _ -> 
      let* overlap = intersect_two p p2 in
      return (alias overlap s)
  | _, PAlias (p, s) -> 
      let* overlap = intersect_two p1 p in
      return (alias overlap s)
  | PConstr (name1, args1), PConstr (name2, args2) when name1 = name2 ->
      let* args = 
        List.combine args1 args2
        |> List.map (fun (arg1, arg2) -> intersect_two arg1 arg2)
        |> cartesian_product
      in
      return (make (PConstr (name1, args)) p1.pattern_type)
  | _, _ -> []

let rec pattern_bindings pat =
  match pat.pattern_desc with
  | PAny | PConstant _ -> []
  | PConstr (_, args) -> List.concat_map pattern_bindings args
  | PVar v -> [v]
  | PAlias (pat, v) -> (v, pat.pattern_type)::(pattern_bindings pat)

let deconflict_renames shared = 
  shared
    |> SMap.to_seq
    |> Seq.map (fun (var, typ) -> (var, (fresh_variable ~v:"patd" (), typ)))
    |> SMap.of_seq

let pi_of_pattern pat_term pat : binder list * pi =
  let conjuncts = ref [] in
  let free_vars = ref [] in
  let add_free_var v = free_vars := v::!free_vars in
  let add_conjunct pi = conjuncts := pi::!conjuncts in
  let new_term_name typ () =
    let v = fresh_variable ~v:"pat" () in add_free_var (v, typ); v in
  let rec inner pat =
    match pat.pattern_desc with
    | PAny ->
        let v = new_term_name pat.pattern_type () in
        var ~typ:pat.pattern_type v
    | PVar v ->
        add_free_var v;
        var ~typ:pat.pattern_type (Untypehip.ident_of_binder v)
    | PConstr (name, args) ->
        term (Construct (name, List.map inner args)) (pat.pattern_type)
    | PConstant c ->
        let v = new_term_name (pat.pattern_type) () in
        let pvar = var ~typ:pat.pattern_type v in
        add_conjunct (eq pvar (term (Const c) pat.pattern_type));
        pvar
    | PAlias (p, v) ->
        let inner_term = inner p in
        let vbinder = (v, pat.pattern_type) in
        add_free_var vbinder;
        add_conjunct (Atomic (EQ, var_of_binder vbinder, inner_term));
        var_of_binder vbinder
  in
  add_conjunct (Atomic (EQ, pat_term, inner pat));
  !free_vars, conj !conjuncts

module Guarded = struct

  let rename_bound_vars bindings ((pat : pattern), (guard : term)) =
    let term_rebindings = SMap.map var_of_binder bindings |> SMap.to_list in
    (* refers to the previous definition without guard clauses *)
    (rename_bound_vars bindings pat, 
      Subst.(subst_free_vars_term term_rebindings guard))

  let intersect (p1s : (pattern * term) list) (p2s : (pattern * term) list) =
    let* p1, g1 = p1s in
    let* p2, g2 = p2s in
    let* overlap = intersect_two p1 p2 in
    let guard_conj =
      match g1.term_desc, g2.term_desc with
      | _, Const TTrue -> g1
      | Const TTrue, _ -> g2
      | _, _ -> tand g1 g2
    in
    return (overlap, guard_conj)

  let complement (pat, guard) =
    let structural = (complement pat |> List.map (fun pat -> (pat, ctrue))) in
    match guard.term_desc with
    (* the guard is always false, so this pattern is empty *)
    | Const TFalse -> [(make PAny pat.pattern_type, ctrue)] 
    (* the guard is always true, so the pattern is always matched against *)
    | Const TTrue -> structural
    (* generally, add the negated guarded pattern to the complement list *)
    | _ -> (pat, tnot guard)::structural

  let deconflict (pat1, _) (pat2, guard2) =
    let shared = SMap.intersect (free_vars_pat pat1) (free_vars_pat pat2) in
    let renames = deconflict_renames shared in
    rename_bound_vars renames (pat2, guard2)

  let exclude pat excluded =
    let excluded = List.map (deconflict pat) excluded in
    List.fold_left intersect [pat] (List.map complement excluded)

  let pi_of_pattern pat_term (pat, guard) =
    let (free_vars, pi) = pi_of_pattern pat_term pat in
    (free_vars, And (pi, eq guard ctrue))

  let pattern_bindings (pat, _) =
    pattern_bindings pat
end

(* shadow the unguarded definitions *)
include Guarded

let guarded ?(condition = ctrue) pat = (pat, condition)

module Testing = struct
  let setup_tests () = 
    let open Globals in
    define_type {
      tdecl_name = "test_type";
      tdecl_params = [TVar "a"];
      tdecl_kind = Tdecl_inductive [
        "A", [];
        "B", [TVar "a"];
        "D", [TConstr ("test_type", [TVar "a"]); TConstr ("test_type", [TVar "a"])]
      ]
    };
    define_type {
      tdecl_name = "nat";
      tdecl_params = [];
      tdecl_kind = Tdecl_inductive [
        "Z", [];
        "S", [TConstr ("nat", [])]
      ]
    }
  open Pretty
  let output pats = String.concat " | " (List.map 
  (fun (pat, guard) ->
    if guard = ctrue
    then string_of_pattern pat
      else Printf.sprintf "%s when %s" (string_of_pattern pat) (string_of_term guard))
  pats) |> print_string

  let any ?(args = []) typ = {pattern_desc = PAny; pattern_type = TConstr (typ, args)}
  let constr ~typ ?(typ_args = []) ctr args  = {pattern_desc = PConstr (ctr, args); pattern_type = TConstr (typ, typ_args)}
  let a = constr ~typ:"test_type" ~typ_args:[Int] "A" []
  let pvar ?(typ="test_type") ?(typ_args=[Int]) name = 
    let typ = TConstr (typ, typ_args) in
    {pattern_desc = PVar (name, typ); pattern_type = typ}
  let b v = constr ~typ:"test_type" ~typ_args:[Int] "B" [v]
  let d (a1, a2) = constr ~typ:"test_type" ~typ_args:[Int] "D" [a1; a2]
  let as_ ~name pat = {pattern_desc = PAlias (pat, name); pattern_type = pat.pattern_type}

  let z = constr ~typ:"nat" "Z" []
  let s n = constr ~typ:"nat" "S" [n]

end


let%expect_test "complement" =
  let open Testing in
  setup_tests ();

  let __ = Testing.any ~args:[Int] "test_type" in
  output (complement (guarded (b __)));
  [%expect{| A() | D(_, _) |}];

  output (complement (guarded (d (b __, a))));
  [%expect{| A() | B(_) | D(B(_), B(_)) | D(B(_), D(_, _)) | D(A(), A()) | D(A(), B(_)) | D(A(), D(_, _)) | D(D(_, _), A()) | D(D(_, _), B(_)) | D(D(_, _), D(_, _)) |}];

  let __ = Testing.any "nat" in
  output (complement (guarded (s (as_ ~name:"s" (s __)))));
  [%expect{| Z() | S((Z()) as s) |}];
;;

let%expect_test "intersect" =
  let open Testing in
  setup_tests ();

  let __ = Testing.any ~args:[Int] "test_type" in
  output (intersect [guarded (d (pvar "a", pvar "b"))] [guarded (b (pvar "x")); guarded (d (__, d (__, pvar "d")))]);
  [%expect{| D(a, (D(_, d)) as b) |}];

  output (intersect [guarded (b __)] [guarded (d (__, __))]);
  [%expect{| |}];

  output (intersect [guarded (d (d (pvar "z", __), __))] [guarded (d (__, d (__, pvar "y")))]);
  [%expect{| D(D(z, _), D(_, y)) |}];
;;

let%expect_test "exclude" =
  let open Testing in

  setup_tests ();

  let __ = Testing.any ~args:[Int] "test_type" in
  output (exclude (guarded (d (__, __))) [guarded a; guarded (d (b __, __))]);
  [%expect{| D(A(), _) | D(D(_, _), _) |}];

  output (exclude (guarded (b __)) []);
  [%expect{| B(_) |}];

  let __ = Testing.any "nat" in
  output (exclude (guarded (s (as_ ~name:"s" z)) ~condition:(rel EQ (var "s") (var "t") )) [guarded z; guarded (s (as_ ~name:"s" (s __)))]);
  [%expect{| S(((Z()) as patd2) as s) when (s==t) |}];
;;
